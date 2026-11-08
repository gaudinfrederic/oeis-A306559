import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# A306559 : suite auto-descriptive voyelles/consonnes (enonce Neder)

Enonce canonique (CIBLES/OEIS/1-PROSPECTION/A306559/VERIFICATIONS/e2-fusion.md) :

- `a : Nat -> Fin 4` avec la graine `a(0)=1, a(1)=2, a(2)=3` ; le mot infini
  est `w = concat_j name(a_j)` sur l'alphabet des 8 lettres de
  ZERO/ONE/TWO/THREE.
- `vpos a k` = position de la (k+1)-eme voyelle dans `w` ;
  `run a k = vpos a (k+1) - vpos a k - 1` = nombre de consonnes
  strictement entre les voyelles n°(k+1) et n°(k+2).
- (EX) pour `aStar = [1,2,3] ++ M` : `run aStar k = (aStar k).val`.
- (UN) toute suite `a` satisfaisant la graine et l'equation est `aStar`.
- `W : 0 -> 11, 1 -> 01` ; `M(0)=0`, `M(2k+1)=(W(M k))[0]`,
  `M(2k+2)=(W(M k))[1]`.

Mecanique (archive Nederpelt, cf. e2-fusion.md) :
- les runs initiaux sont `ONE|TWO = [1,2]` puis `THREE = [3,0]` ;
- dans la zone morphique (`ZERO`/`ONE` seuls), chaque bloc `name(M j)`
  produit exactement deux voyelles, donc deux runs :
  `[run interne, run de bordure] = [1, 1 - M(j+1)] = W(M j)` ;
- le mot morphique est ainsi point fixe de la description.

Conventions : les indices de blocs apres la graine sont ecrits `j + 3`
(litteral a droite) pour correspondre a la branche `k + 3` de `aStar306559`.

NOTE DE CALCULABILITE : `Nat.digits` de Mathlib est defini par recursion
bien-fondee (`digitsAux`, `decreasing_by`) et n'est PAS reducible par le
noyau (`decide` ne l'evalue pas). On utilise donc `bits306559`, une
version a carburant structurellement recursive, pour que tous les
ancrages (`run`, `vpos`, `M`, `aStar`) restent calculables par `decide`.
-/

namespace A306559

/-- Alphabet : les huit lettres distinctes de ZERO/ONE/TWO/THREE. -/
inductive Letter306559 | O | N | E | T | W | Z | R | H
  deriving DecidableEq

/-- Test de voyelle : seuls `E` et `O` sont des voyelles. -/
def isVowel306559 : Letter306559 → Bool
  | .O => true
  | .E => true
  | _ => false

/-- Nom anglais de `c : Fin 4` : ZERO, ONE, TWO, THREE. -/
def name306559 (c : Fin 4) : List Letter306559 :=
  match c.val with
  | 0 => [.Z, .E, .R, .O]
  | 1 => [.O, .N, .E]
  | 2 => [.T, .W, .O]
  | _ => [.T, .H, .R, .E, .E]

/-- Iteration structurelle (version locale, reduction iota directe). -/
def iter306559 {α : Type} (f : α → α) : ℕ → α → α
  | 0, x => x
  | n + 1, x => f (iter306559 f n x)

/-- Un pas de lecture : dans le bloc courant, ou passage au bloc
    suivant quand on a depasse la derniere lettre. -/
def step306559 (a : ℕ → Fin 4) (s : ℕ × ℕ) : ℕ × ℕ :=
  if s.2 + 1 < (name306559 (a s.1)).length
    then (s.1, s.2 + 1)
    else (s.1 + 1, 0)

/-- Le mot infini : la i-eme lettre de `concat name(a_j)`.
    `iter306559 (step a) i (0,0)` calcule la paire (bloc, offset). -/
def wordOf306559 (a : ℕ → Fin 4) (i : ℕ) : Letter306559 :=
  (name306559 (a (iter306559 (step306559 a) i (0, 0)).1)).getD
    (iter306559 (step306559 a) i (0, 0)).2 Letter306559.O

/-- Longueur cumulee : `cum a j` = position de debut du bloc `j`. -/
def cum306559 (a : ℕ → Fin 4) : ℕ → ℕ
  | 0 => 0
  | j + 1 => cum306559 a j + (name306559 (a j)).length

/-- Premiere position `>= p` portant une voyelle, a carburant borne.
    Le carburant 5 suffit : tout nom finit par une voyelle et a
    longueur `<= 5`, donc une voyelle est toujours a distance `<= 4`. -/
def nextVowel306559 (a : ℕ → Fin 4) (p : ℕ) : ℕ → ℕ
  | 0 => p
  | f + 1 =>
    if isVowel306559 (wordOf306559 a p) then p
    else nextVowel306559 a (p + 1) f

/-- `vpos a k` = position de la (k+1)-eme voyelle du mot. -/
def vpos306559 (a : ℕ → Fin 4) : ℕ → ℕ
  | 0 => nextVowel306559 a 0 5
  | k + 1 => nextVowel306559 a (vpos306559 a k + 1) 5

/-- `run a k` = consonnes strictement entre les voyelles n°(k+1), (k+2). -/
def run306559 (a : ℕ → Fin 4) (k : ℕ) : ℕ :=
  vpos306559 a (k + 1) - vpos306559 a k - 1

/-- Morphisme canonique `W : 0 -> 11, 1 -> 01`. -/
def W306559 (b : Fin 2) : List (Fin 2) := if b = 0 then [1, 1] else [0, 1]

/-- Un pas de l'automate de `M` : `s -> (W s)[b]`. -/
def Mstep306559 (s : Fin 2) (b : ℕ) : Fin 2 := (W306559 s).getD b 0

/-- Chiffres binaires de `n`, bit de poids faible en tete, a carburant
    (structurel, reducible par le noyau). `f >= n+1` suffit toujours. -/
def bitsAux306559 : ℕ → ℕ → List ℕ
  | 0, _ => []
  | f + 1, n => if n = 0 then [] else (n % 2) :: bitsAux306559 f (n / 2)

/-- Chiffres binaires de `n` (LSB en tete). -/
def bits306559 (n : ℕ) : List ℕ := bitsAux306559 (n + 1) n

/-- Corps de `M` : fold `s -> W(s)[b]` sur les bits de `n` sous le MSB,
    traites du MSB vers le LSB, etat initial 0. -/
def Mfold306559 (n : ℕ) : Fin 2 :=
  ((bits306559 n).dropLast.reverse).foldl Mstep306559 0

/-- La suite morphique de Neder : `M(n) = fold_{bits(n+1)\MSB} W`. -/
def M306559 (n : ℕ) : Fin 2 := Mfold306559 (n + 1)

/-- La suite candidate : graine `[1,2,3]` puis la queue `M`. -/
def aStar306559 : ℕ → Fin 4
  | 0 => 1
  | 1 => 2
  | 2 => 3
  | k + 3 => (M306559 k).castLE (by norm_num)

/-- Premier offset de voyelle dans `name(b)` pour `b : Fin 2`
    (ZERO : 1, ONE : 0). -/
def off1306559 (b : Fin 2) : ℕ := if b = 0 then 1 else 0

/-- Dernier offset de voyelle (ZERO : 3, ONE : 2). -/
def off2306559 (b : Fin 2) : ℕ := if b = 0 then 3 else 2

/-- Longueur de `name(b)` pour `b : Fin 2` (ZERO : 4, ONE : 3). -/
def nlen306559 (b : Fin 2) : ℕ := if b = 0 then 4 else 3

/-- (EX) existence : aStar est point fixe auto-descriptif. -/
abbrev conjectureEX306559 : Prop :=
  ∀ k : ℕ, run306559 aStar306559 k = (aStar306559 k).val

/-- (UN) unicite sous la graine `[1,2,3]`. -/
abbrev conjectureUN306559 : Prop :=
  ∀ a : ℕ → Fin 4,
    a 0 = 1 → a 1 = 2 → a 2 = 3 →
    (∀ k : ℕ, run306559 a k = (a k).val) → a = aStar306559

end A306559

open A306559

/-! ## Faits elementaires sur les noms et les offsets -/

theorem name306559_len_pos (c : Fin 4) : 0 < (name306559 c).length := by
  fin_cases c <;> decide

theorem name306559_len_ge3 (c : Fin 4) : 3 ≤ (name306559 c).length := by
  fin_cases c <;> decide

theorem fin2_eq_zero_or_one (b : Fin 2) : b = 0 ∨ b = 1 := by
  fin_cases b <;> simp

theorem nlen306559_pos (b : Fin 2) : 0 < nlen306559 b := by
  rcases fin2_eq_zero_or_one b with h | h <;> rw [h] <;> decide

theorem nlen306559_sub_off2 (b : Fin 2) : nlen306559 b - off2306559 b = 1 := by
  rcases fin2_eq_zero_or_one b with h | h <;> rw [h] <;> decide

theorem off2_sub_off1 (b : Fin 2) : off2306559 b - off1306559 b = 2 := by
  rcases fin2_eq_zero_or_one b with h | h <;> rw [h] <;> decide

theorem off1_eq306559 (b : Fin 2) : off1306559 b = 1 - b.val := by
  rcases fin2_eq_zero_or_one b with h | h <;> rw [h] <;> decide

theorem off2_eq_nlen_sub_one (b : Fin 2) : off2306559 b = nlen306559 b - 1 := by
  rcases fin2_eq_zero_or_one b with h | h <;> rw [h] <;> decide

theorem off1_lt_nlen (b : Fin 2) : off1306559 b < nlen306559 b := by
  rcases fin2_eq_zero_or_one b with h | h <;> rw [h] <;> decide

theorem off2_lt_nlen (b : Fin 2) : off2306559 b < nlen306559 b := by
  rcases fin2_eq_zero_or_one b with h | h <;> rw [h] <;> decide

/-- `name306559` ne voit que `Fin.val` : on remplace `b.castLE h` par
    une forme en `b` sans temoin de preuve, pour que `decide` ne voie
    plus la variable libre `h` (le noyau refuse les buts contenant
    des variables libres). -/
theorem name306559_castLE (b : Fin 2) (h : 2 ≤ 4) :
    name306559 (b.castLE h) =
      (if b = 0 then [.Z, .E, .R, .O] else [.O, .N, .E]) := by
  rcases fin2_eq_zero_or_one b with h' | h' <;> rw [h'] <;> rfl

theorem name_castLE_len (b : Fin 2) (h : 2 ≤ 4) :
    (name306559 (b.castLE h)).length = nlen306559 b := by
  rw [name306559_castLE b h]
  rcases fin2_eq_zero_or_one b with h' | h' <;> rw [h'] <;> decide

/-- Les lettres sous le premier offset voyelle sont des consonnes. -/
theorem name_castLE_getD_lt_off1 (b : Fin 2) (h : 2 ≤ 4) (i : ℕ)
    (hi : i < off1306559 b) :
    isVowel306559 ((name306559 (b.castLE h)).getD i Letter306559.O) = false := by
  rw [name306559_castLE b h]
  rcases fin2_eq_zero_or_one b with h' | h' <;> rw [h'] at hi ⊢
  · rw [show off1306559 (0 : Fin 2) = 1 by decide] at hi
    interval_cases i <;> decide
  · rw [show off1306559 (1 : Fin 2) = 0 by decide] at hi
    exact absurd hi (Nat.not_lt_zero i)

/-- Les lettres strictement entre les deux offsets voyelles : consonnes. -/
theorem name_castLE_getD_mid (b : Fin 2) (h : 2 ≤ 4) (i : ℕ)
    (h1 : off1306559 b < i) (h2 : i < off2306559 b) :
    isVowel306559 ((name306559 (b.castLE h)).getD i Letter306559.O) = false := by
  rw [name306559_castLE b h]
  rcases fin2_eq_zero_or_one b with h' | h' <;> rw [h'] at h1 h2 ⊢
  · rw [show off1306559 (0 : Fin 2) = 1 by decide] at h1
    rw [show off2306559 (0 : Fin 2) = 3 by decide] at h2
    interval_cases i <;> decide
  · rw [show off1306559 (1 : Fin 2) = 0 by decide] at h1
    rw [show off2306559 (1 : Fin 2) = 2 by decide] at h2
    interval_cases i <;> decide

/-- La lettre au premier offset est une voyelle. -/
theorem name_castLE_getD_off1 (b : Fin 2) (h : 2 ≤ 4) :
    isVowel306559 ((name306559 (b.castLE h)).getD (off1306559 b)
      Letter306559.O) = true := by
  rw [name306559_castLE b h]
  rcases fin2_eq_zero_or_one b with h' | h' <;> rw [h'] <;> decide

/-- La lettre au dernier offset est une voyelle. -/
theorem name_castLE_getD_off2 (b : Fin 2) (h : 2 ≤ 4) :
    isVowel306559 ((name306559 (b.castLE h)).getD (off2306559 b)
      Letter306559.O) = true := by
  rw [name306559_castLE b h]
  rcases fin2_eq_zero_or_one b with h' | h' <;> rw [h'] <;> decide

/-! ## Lemmes sur `iter306559` -/

theorem iter306559_add {α : Type} (f : α → α) (m n : ℕ) (x : α) :
    iter306559 f (m + n) x = iter306559 f n (iter306559 f m x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      show f (iter306559 f (m + n) x) = f (iter306559 f n (iter306559 f m x))
      rw [ih]

/-- Invariant dans un bloc : `r` pas depuis (j,0) menant a (j,r) si
    `r < len`, sinon a (j+1,0) a `r = len`. -/
theorem iter_within306559 (a : ℕ → Fin 4) (j r : ℕ)
    (hr : r ≤ (name306559 (a j)).length) :
    iter306559 (step306559 a) r (j, 0) =
      if r < (name306559 (a j)).length then (j, r) else (j + 1, 0) := by
  revert hr
  induction r with
  | zero =>
      intro _
      have hpos : 0 < (name306559 (a j)).length := name306559_len_pos _
      rw [if_pos hpos]
      rfl
  | succ r ih =>
      intro hr
      have hr' : r ≤ (name306559 (a j)).length := by omega
      have hrr : r < (name306559 (a j)).length := by omega
      show step306559 a (iter306559 (step306559 a) r (j, 0)) = _
      rw [ih hr', if_pos hrr]
      -- `step306559 a (j, r)` se reduit a
      -- `if r+1 < len then (j,r+1) else (j+1,0)` ; les deux membres
      -- sont alors identiques
      rfl

/-- `iter_cum` : le debut du bloc `j` est l'etat (j,0). -/
theorem iter_cum306559 (a : ℕ → Fin 4) (j : ℕ) :
    iter306559 (step306559 a) (cum306559 a j) (0, 0) = (j, 0) := by
  induction j with
  | zero => rfl
  | succ j ih =>
      show iter306559 (step306559 a) (cum306559 a j + (name306559 (a j)).length)
          (0, 0) = (j + 1, 0)
      rw [iter306559_add, ih]
      rw [iter_within306559 a j (name306559 (a j)).length (le_refl _)]
      rw [if_neg (show ¬ (name306559 (a j)).length <
                          (name306559 (a j)).length by omega)]

theorem iter_at306559 (a : ℕ → Fin 4) (j r : ℕ)
    (hr : r < (name306559 (a j)).length) :
    iter306559 (step306559 a) (cum306559 a j + r) (0, 0) = (j, r) := by
  rw [iter306559_add, iter_cum306559, iter_within306559 a j r (le_of_lt hr),
      if_pos hr]

theorem wordOf_eq306559 (a : ℕ → Fin 4) (j r : ℕ)
    (hr : r < (name306559 (a j)).length) :
    wordOf306559 a (cum306559 a j + r) =
      (name306559 (a j)).getD r Letter306559.O := by
  show (name306559 (a (iter306559 (step306559 a) (cum306559 a j + r) (0, 0)).1)).getD
      (iter306559 (step306559 a) (cum306559 a j + r) (0, 0)).2 Letter306559.O = _
  rw [iter_at306559 a j r hr]

/-- Invariant global de l'iterateur : toute position lue est une
    decomposition (bloc, offset) valide. -/
theorem iter_invariant306559 (a : ℕ → Fin 4) (i : ℕ) :
    ∃ j r, iter306559 (step306559 a) i (0, 0) = (j, r) ∧
      i = cum306559 a j + r ∧ r < (name306559 (a j)).length := by
  induction i with
  | zero => exact ⟨0, 0, rfl, rfl, name306559_len_pos _⟩
  | succ i ih =>
      obtain ⟨j, r, hit, hij, hrj⟩ := ih
      have e : iter306559 (step306559 a) (i + 1) (0, 0) = step306559 a (j, r) := by
        show step306559 a (iter306559 (step306559 a) i (0, 0)) = _
        rw [hit]
      rw [e]
      by_cases h : r + 1 < (name306559 (a j)).length
      · refine ⟨j, r + 1, ?_, by omega, h⟩
        show (if r + 1 < (name306559 (a j)).length
              then (j, r + 1) else (j + 1, 0)) = (j, r + 1)
        rw [if_pos h]
      · refine ⟨j + 1, 0, ?_, ?_, name306559_len_pos _⟩
        · show (if r + 1 < (name306559 (a j)).length
                then (j, r + 1) else (j + 1, 0)) = (j + 1, 0)
          rw [if_neg h]
        · have hr1 : r + 1 = (name306559 (a j)).length := by omega
          show i + 1 = cum306559 a j + (name306559 (a j)).length
          omega

/-! ## Lemmes sur `nextVowel306559` et `vpos306559` -/

/-- `nextVowel` atteint `p + d` quand les positions de `[p, p+d)` sont
    des consonnes et `p+d` est une voyelle. -/
theorem nextVowel_eq306559 (a : ℕ → Fin 4) (p d : ℕ) (fuel : ℕ)
    (hdf : d ≤ fuel)
    (hcons : ∀ i : ℕ, p ≤ i → i < p + d →
      isVowel306559 (wordOf306559 a i) = false)
    (hvow : isVowel306559 (wordOf306559 a (p + d)) = true) :
    nextVowel306559 a p fuel = p + d := by
  induction d generalizing p fuel with
  | zero =>
      cases fuel with
      | zero => rfl
      | succ f =>
          show (if isVowel306559 (wordOf306559 a p) then p
                else nextVowel306559 a (p + 1) f) = p
          have hvow' : isVowel306559 (wordOf306559 a p) = true := hvow
          rw [if_pos hvow']
  | succ d ih =>
      cases fuel with
      | zero => omega
      | succ f =>
          have hp : isVowel306559 (wordOf306559 a p) = false :=
            hcons p (le_refl p) (by omega)
          show (if isVowel306559 (wordOf306559 a p) then p
                else nextVowel306559 a (p + 1) f) = p + (d + 1)
          rw [if_neg (show ¬ (isVowel306559 (wordOf306559 a p) = true) by
              simp [hp])]
          have e : p + (d + 1) = (p + 1) + d := by omega
          rw [e]
          exact ih (p + 1) f (by omega)
            (fun i hi h'i => hcons i (by omega) (by omega))
            (by rwa [show (p + 1) + d = p + (d + 1) by omega])

theorem nextVowel_ge306559 (a : ℕ → Fin 4) (p f : ℕ) :
    p ≤ nextVowel306559 a p f := by
  induction f generalizing p with
  | zero => exact le_refl p
  | succ f ih =>
      show p ≤ (if isVowel306559 (wordOf306559 a p) then p
                else nextVowel306559 a (p + 1) f)
      by_cases h' : isVowel306559 (wordOf306559 a p) = true
      · rw [if_pos h']
      · rw [if_neg h']; exact (by omega : p ≤ p + 1).trans (ih (p + 1))

/-- Avant `nextVowel`, toute position est une consonne (meme si le
    carburant est epuise : la borne reste valide). -/
theorem nextVowel_lt_not_vowel306559 (a : ℕ → Fin 4) (p f i : ℕ)
    (hp : p ≤ i) (hi : i < nextVowel306559 a p f) :
    isVowel306559 (wordOf306559 a i) = false := by
  induction f generalizing p i with
  | zero =>
      have hi' : i < p := hi
      omega
  | succ f ih =>
      have hi' : i < (if isVowel306559 (wordOf306559 a p) then p
                else nextVowel306559 a (p + 1) f) := hi
      by_cases h' : isVowel306559 (wordOf306559 a p) = true
      · rw [if_pos h'] at hi'; omega
      · rw [if_neg h'] at hi'
        rcases lt_or_eq_of_le hp with hpi | rfl
        · exact ih (p + 1) i hpi hi'
        · exact (Bool.not_eq_true _).mp h'

theorem vpos_lt_succ306559 (a : ℕ → Fin 4) (n : ℕ) :
    vpos306559 a n < vpos306559 a (n + 1) := by
  show vpos306559 a n < nextVowel306559 a (vpos306559 a n + 1) 5
  have := nextVowel_ge306559 a (vpos306559 a n + 1) 5
  omega

theorem vpos_lt_of_lt306559 (a : ℕ → Fin 4) {m n : ℕ} (h : m < n) :
    vpos306559 a m < vpos306559 a n := by
  revert h
  induction n with
  | zero => intro h'; omega
  | succ n ih =>
      intro h'
      rcases lt_or_eq_of_le (Nat.le_of_lt_succ h') with hlt | rfl
      · exact (ih hlt).trans (vpos_lt_succ306559 a n)
      · exact vpos_lt_succ306559 a m

/-- Accord de `nextVowel` entre deux mots qui coincident sur la fenetre
    `[p, p+d]` (b controle la forme du resultat). -/
theorem nextVowel_agree306559 (a b : ℕ → Fin 4) (p d f : ℕ)
    (hvow : isVowel306559 (wordOf306559 b (p + d)) = true)
    (hcon : ∀ i : ℕ, p ≤ i → i < p + d →
      isVowel306559 (wordOf306559 b i) = false)
    (h : ∀ i : ℕ, p ≤ i → i ≤ p + d →
      wordOf306559 a i = wordOf306559 b i)
    (hdf : d ≤ f) :
    nextVowel306559 a p f = p + d := by
  apply nextVowel_eq306559 a p d f hdf
  · intro i hi h'i
    rw [h i hi (by omega)]
    exact hcon i hi h'i
  · rw [h (p + d) (Nat.le_add_right p d) (le_refl _)]
    exact hvow

/-! ## La suite morphique `M306559` -/

/-- Exces de carburant inoffensif : pour `f, g >= n+1`, le resultat ne
    depend pas du carburant. -/
theorem bitsAux306559_fuel (f : ℕ) : ∀ (g n : ℕ),
    n + 1 ≤ f → n + 1 ≤ g → bitsAux306559 f n = bitsAux306559 g n := by
  induction f with
  | zero => intro g n hf hg; omega
  | succ f ih =>
      intro g n hf hg
      cases g with
      | zero => omega
      | succ g =>
          cases n with
          | zero => rfl
          | succ n =>
              show (if (n + 1) = 0 then []
                    else (n + 1) % 2 :: bitsAux306559 f ((n + 1) / 2)) =
                   (if (n + 1) = 0 then []
                    else (n + 1) % 2 :: bitsAux306559 g ((n + 1) / 2))
              rw [if_neg (by omega), if_neg (by omega)]
              exact congrArg _ (ih g ((n + 1) / 2) (by omega) (by omega))

theorem bits306559_ne_nil (m : ℕ) (hm : 0 < m) : bits306559 m ≠ [] := by
  show bitsAux306559 (m + 1) m ≠ []
  show (if m = 0 then [] else m % 2 :: bitsAux306559 m (m / 2)) ≠ []
  rw [if_neg (by omega)]
  exact List.cons_ne_nil _ _

theorem bits306559_bit0 (m : ℕ) (hm : 0 < m) :
    bits306559 (2 * m) = 0 :: bits306559 m := by
  show bitsAux306559 (2 * m + 1) (2 * m) = 0 :: bitsAux306559 (m + 1) m
  show (if 2 * m = 0 then []
        else (2 * m) % 2 :: bitsAux306559 (2 * m) (2 * m / 2)) = _
  rw [if_neg (by omega)]
  have e1 : 2 * m % 2 = 0 := by omega
  have e2 : 2 * m / 2 = m := by omega
  rw [e1, e2, bitsAux306559_fuel (2 * m) (m + 1) m (by omega) (by omega)]

theorem bits306559_bit1 (m : ℕ) :
    bits306559 (2 * m + 1) = 1 :: bits306559 m := by
  show bitsAux306559 (2 * m + 2) (2 * m + 1) = 1 :: bitsAux306559 (m + 1) m
  show (if 2 * m + 1 = 0 then []
        else (2 * m + 1) % 2 :: bitsAux306559 (2 * m + 1) ((2 * m + 1) / 2)) = _
  rw [if_neg (by omega)]
  have e1 : (2 * m + 1) % 2 = 1 := by omega
  have e2 : (2 * m + 1) / 2 = m := by omega
  rw [e1, e2, bitsAux306559_fuel (2 * m + 1) (m + 1) m (by omega) (by omega)]

theorem dropLast_cons306559 {α : Type} (a : α) (l : List α) (hl : l ≠ []) :
    (a :: l).dropLast = a :: l.dropLast := by
  cases l with
  | nil => exact absurd rfl hl
  | cons b t => rw [List.dropLast_cons_cons]

theorem M306559_zero : M306559 0 = 0 := by decide

theorem M306559_odd (k : ℕ) :
    M306559 (2 * k + 1) = (W306559 (M306559 k)).getD 0 0 := by
  have e : M306559 (2 * k + 1) = Mfold306559 (2 * (k + 1)) := rfl
  rw [e]
  show (((bits306559 (2 * (k + 1))).dropLast.reverse).foldl Mstep306559 0) = _
  rw [bits306559_bit0 (k + 1) (Nat.succ_pos k),
      dropLast_cons306559 0 _ (bits306559_ne_nil (k + 1) (Nat.succ_pos k)),
      List.reverse_cons, List.foldl_append]
  show Mstep306559 (((bits306559 (k + 1)).dropLast.reverse).foldl Mstep306559 0)
      0 = _
  rfl

theorem M306559_even (k : ℕ) :
    M306559 (2 * k + 2) = (W306559 (M306559 k)).getD 1 0 := by
  have e : M306559 (2 * k + 2) = Mfold306559 (2 * (k + 1) + 1) := rfl
  rw [e]
  show (((bits306559 (2 * (k + 1) + 1)).dropLast.reverse).foldl Mstep306559 0) = _
  rw [bits306559_bit1 (k + 1),
      dropLast_cons306559 1 _ (bits306559_ne_nil (k + 1) (Nat.succ_pos k)),
      List.reverse_cons, List.foldl_append]
  show Mstep306559 (((bits306559 (k + 1)).dropLast.reverse).foldl Mstep306559 0)
      1 = _
  rfl

theorem M306559_even_one (j : ℕ) : M306559 (2 * j + 2) = 1 := by
  rw [M306559_even]
  rcases fin2_eq_zero_or_one (M306559 j) with hm | hm <;> rw [hm] <;> decide

theorem M306559_odd_neg (j : ℕ) :
    (M306559 (2 * j + 1)).val = 1 - (M306559 j).val := by
  rw [M306559_odd]
  rcases fin2_eq_zero_or_one (M306559 j) with hm | hm <;> rw [hm] <;> decide

/-! ## `aStar306559` : graine et queue -/

theorem aStar306559_tail (k : ℕ) :
    aStar306559 (k + 3) = (M306559 k).castLE (by norm_num) := rfl

theorem aStar306559_val (k : ℕ) :
    (aStar306559 (k + 3)).val = (M306559 k).val := rfl

theorem cum306559_succ (a : ℕ → Fin 4) (n : ℕ) :
    cum306559 a (n + 1) = cum306559 a n + (name306559 (a n)).length := by
  simp only [cum306559]

theorem cum_mono306559 (a : ℕ → Fin 4) {j k : ℕ} (h : j ≤ k) :
    cum306559 a j ≤ cum306559 a k := by
  revert h
  induction k with
  | zero =>
      intro h
      have h0 : j = 0 := by omega
      subst h0
      exact le_refl _
  | succ k ih =>
      intro h
      rcases lt_or_eq_of_le h with hlt | rfl
      · exact (ih (by omega)).trans (by rw [cum306559_succ]; omega)
      · exact le_refl _

theorem cum_congr306559 (a b : ℕ → Fin 4) (k j : ℕ)
    (h : ∀ j', j' < k → name306559 (a j') = name306559 (b j'))
    (hj : j ≤ k) : cum306559 a j = cum306559 b j := by
  revert hj
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
      intro hj
      have hjj : j < k := by omega
      rw [cum306559_succ, cum306559_succ, ih (by omega), h j hjj]

theorem len_aStar306559 (j : ℕ) :
    (name306559 (aStar306559 (j + 3))).length = nlen306559 (M306559 j) := by
  rw [aStar306559_tail]
  exact name_castLE_len (M306559 j) _

theorem cum_aStar306559 (j : ℕ) :
    cum306559 aStar306559 (j + 4) =
      cum306559 aStar306559 (j + 3) + nlen306559 (M306559 j) := by
  rw [show (j + 4 : ℕ) = (j + 3) + 1 by omega, cum306559_succ, len_aStar306559]

/-! ## Ancres numeriques (verification `decide`) -/

/-- Positions initiales des voyelles :
    ONE(0..2) TWO(3..5) THREE(6..10) ZERO(11..14) ONE(15..17) ONE(18..20)
    voyelles aux positions 0, 2, 5, 9, 10, 12, 14, 15, 17, ...
    (runs : 1,2,3,0,1,1,0,1,0,1 - le mot s'auto-decrit). -/
theorem vpos_aStar306559_0 : vpos306559 aStar306559 0 = 0 := by decide
theorem vpos_aStar306559_1 : vpos306559 aStar306559 1 = 2 := by decide
theorem vpos_aStar306559_2 : vpos306559 aStar306559 2 = 5 := by decide
theorem vpos_aStar306559_3 : vpos306559 aStar306559 3 = 9 := by decide
theorem vpos_aStar306559_4 : vpos306559 aStar306559 4 = 10 := by decide
theorem vpos_aStar306559_5 : vpos306559 aStar306559 5 = 12 := by decide
theorem vpos_aStar306559_6 : vpos306559 aStar306559 6 = 14 := by decide
theorem cum_aStar306559_3 : cum306559 aStar306559 3 = 11 := by decide

/-! ## Lemme porteur : les deux voyelles du bloc `j+3`

    Depuis `vpos aStar 5 = 12`, les voyelles sont exactement les deux
    voyelles de chaque bloc `name(M j)` : `vpos(5+2j)` et `vpos(6+2j)`
    sont les offsets interne `off1` et final `off2` du bloc `j+3`. -/

theorem vpos_pair306559 (j : ℕ) :
    vpos306559 aStar306559 (5 + 2 * j) =
        cum306559 aStar306559 (j + 3) + off1306559 (M306559 j) ∧
    vpos306559 aStar306559 (6 + 2 * j) =
        cum306559 aStar306559 (j + 3) + off2306559 (M306559 j) := by
  induction j with
  | zero =>
      constructor
      · show vpos306559 aStar306559 5 = _
        rw [vpos_aStar306559_5]
        have hm0 : M306559 0 = 0 := by decide
        rw [show (0 + 3 : ℕ) = 3 by omega, hm0]
        decide
      · show vpos306559 aStar306559 6 = _
        rw [vpos_aStar306559_6]
        have hm0 : M306559 0 = 0 := by decide
        rw [show (0 + 3 : ℕ) = 3 by omega, hm0]
        decide
  | succ j ih =>
      obtain ⟨ih5, ih6⟩ := ih
      -- Moitie gauche : premiere voyelle du bloc j+4 (bordure).
      have hfirst : vpos306559 aStar306559 (5 + 2 * (j + 1)) =
          cum306559 aStar306559 (j + 4) + off1306559 (M306559 (j + 1)) := by
        rw [show (5 + 2 * (j + 1) : ℕ) = 6 + 2 * j + 1 by omega]
        show nextVowel306559 aStar306559
            (vpos306559 aStar306559 (6 + 2 * j) + 1) 5 = _
        rw [ih6]
        -- cum(j+3) + off2 + 1 = cum(j+4) car off2 = nlen - 1
        have hc : cum306559 aStar306559 (j + 3) + off2306559 (M306559 j) + 1 =
                  cum306559 aStar306559 (j + 4) := by
          rw [cum_aStar306559, off2_eq_nlen_sub_one]
          have hp : 0 < nlen306559 (M306559 j) := nlen306559_pos _
          omega
        rw [hc]
        apply nextVowel_eq306559 aStar306559 _ (off1306559 (M306559 (j + 1))) 5
        · -- d = off1 <= 1 <= 5
          rcases fin2_eq_zero_or_one (M306559 (j + 1)) with hm | hm <;>
            rw [hm] <;> decide
        · -- consonnes avant la premiere voyelle : offsets < off1
          intro i hi h'i
          rcases fin2_eq_zero_or_one (M306559 (j + 1)) with hm | hm
          · -- M(j+1) = 0 : off1 = 1, seul i = cum(j+4) (offset 0 = Z)
            rw [hm] at h'i
            have heq : i = cum306559 aStar306559 (j + 4) := by
              have : off1306559 (0 : Fin 2) = 1 := by decide
              omega
            subst heq
            show isVowel306559
                (wordOf306559 aStar306559 (cum306559 aStar306559 (j + 4) + 0)) =
                false
            rw [wordOf_eq306559 aStar306559 (j + 4) 0
                  (by rw [show (j + 4 : ℕ) = (j + 1) + 3 by omega,
                          len_aStar306559, hm]; decide),
                show (j + 4 : ℕ) = (j + 1) + 3 by omega,
                aStar306559_tail, hm]
            exact name_castLE_getD_lt_off1 (0 : Fin 2) _ 0 (by decide)
          · -- M(j+1) = 1 : off1 = 0, intervalle vide
            rw [hm] at h'i
            have : off1306559 (1 : Fin 2) = 0 := by decide
            omega
        · -- extremite : premiere voyelle du bloc
          rcases fin2_eq_zero_or_one (M306559 (j + 1)) with hm | hm
          · rw [hm]
            rw [wordOf_eq306559 aStar306559 (j + 4) (off1306559 (0 : Fin 2))
                  (by rw [show (j + 4 : ℕ) = (j + 1) + 3 by omega,
                          len_aStar306559, hm]; decide),
                show (j + 4 : ℕ) = (j + 1) + 3 by omega,
                aStar306559_tail, hm]
            exact name_castLE_getD_off1 (0 : Fin 2) _
          · rw [hm]
            rw [wordOf_eq306559 aStar306559 (j + 4) (off1306559 (1 : Fin 2))
                  (by rw [show (j + 4 : ℕ) = (j + 1) + 3 by omega,
                          len_aStar306559, hm]; decide),
                show (j + 4 : ℕ) = (j + 1) + 3 by omega,
                aStar306559_tail, hm]
            exact name_castLE_getD_off1 (1 : Fin 2) _
      -- Moitie droite : derniere voyelle du bloc j+4 (interne).
      have hsecond : vpos306559 aStar306559 (6 + 2 * (j + 1)) =
          cum306559 aStar306559 (j + 4) + off2306559 (M306559 (j + 1)) := by
        rw [show (6 + 2 * (j + 1) : ℕ) = 5 + 2 * (j + 1) + 1 by omega]
        show nextVowel306559 aStar306559
            (vpos306559 aStar306559 (5 + 2 * (j + 1)) + 1) 5 = _
        rw [hfirst]
        have eeq : cum306559 aStar306559 (j + 4) + off2306559 (M306559 (j + 1)) =
            cum306559 aStar306559 (j + 4) + off1306559 (M306559 (j + 1)) + 1 +
            (off2306559 (M306559 (j + 1)) - off1306559 (M306559 (j + 1)) - 1) := by
          have := off2_sub_off1 (M306559 (j + 1)); omega
        rw [eeq]
        apply nextVowel_eq306559 aStar306559 _
          (off2306559 (M306559 (j + 1)) - off1306559 (M306559 (j + 1)) - 1) 5
        · have := off2_sub_off1 (M306559 (j + 1)); omega
        · -- consonnes intermediaires : offsets dans `]off1, off2[`
          intro i hi h'i
          obtain ⟨r, hi', hr⟩ : ∃ r : ℕ, i = cum306559 aStar306559 (j + 4) +
              off1306559 (M306559 (j + 1)) + 1 + r ∧
              r < off2306559 (M306559 (j + 1)) - off1306559 (M306559 (j + 1)) - 1 :=
            ⟨i - (cum306559 aStar306559 (j + 4) + off1306559 (M306559 (j + 1)) + 1),
             by omega, by omega⟩
          subst hi'
          have hoff : off1306559 (M306559 (j + 1)) <
                off1306559 (M306559 (j + 1)) + 1 + r ∧
              off1306559 (M306559 (j + 1)) + 1 + r < off2306559 (M306559 (j + 1)) := by
            omega
          rw [show cum306559 aStar306559 (j + 4) + off1306559 (M306559 (j + 1)) +
                  1 + r =
                cum306559 aStar306559 (j + 4) +
                  (off1306559 (M306559 (j + 1)) + 1 + r) by omega,
              wordOf_eq306559 aStar306559 (j + 4)
                (off1306559 (M306559 (j + 1)) + 1 + r)
                (by rw [show (j + 4 : ℕ) = (j + 1) + 3 by omega, len_aStar306559]
                    have := off2_lt_nlen (M306559 (j + 1)); omega),
              show (j + 4 : ℕ) = (j + 1) + 3 by omega,
              aStar306559_tail]
          exact name_castLE_getD_mid (M306559 (j + 1)) _ _ hoff.1 hoff.2
        · -- extremite : derniere voyelle du bloc
          have hsub := off2_sub_off1 (M306559 (j + 1))
          rw [show cum306559 aStar306559 (j + 4) + off1306559 (M306559 (j + 1)) +
                  1 + (off2306559 (M306559 (j + 1)) - off1306559 (M306559 (j + 1))
                    - 1) =
                cum306559 aStar306559 (j + 4) + off2306559 (M306559 (j + 1)) by
                omega,
              wordOf_eq306559 aStar306559 (j + 4) (off2306559 (M306559 (j + 1)))
                (by rw [show (j + 4 : ℕ) = (j + 1) + 3 by omega, len_aStar306559]
                    exact off2_lt_nlen _),
              show (j + 4 : ℕ) = (j + 1) + 3 by omega,
              aStar306559_tail]
          exact name_castLE_getD_off2 (M306559 (j + 1)) _
      exact ⟨hfirst, hsecond⟩

/-! ## Runs de la zone morphique -/

theorem run_pair306559 (j : ℕ) :
    run306559 aStar306559 (5 + 2 * j) = (aStar306559 (5 + 2 * j)).val ∧
    run306559 aStar306559 (6 + 2 * j) = (aStar306559 (6 + 2 * j)).val := by
  obtain ⟨h51, h52⟩ := vpos_pair306559 j
  obtain ⟨h61, _⟩ := vpos_pair306559 (j + 1)
  constructor
  · -- run interne : off2 - off1 - 1 = 1 = M(2j+2)
    show vpos306559 aStar306559 (5 + 2 * j + 1) -
         vpos306559 aStar306559 (5 + 2 * j) - 1 = _
    rw [show (5 + 2 * j + 1 : ℕ) = 6 + 2 * j by omega, h51, h52]
    have e1 : off2306559 (M306559 j) - off1306559 (M306559 j) - 1 = 1 := by
      rcases fin2_eq_zero_or_one (M306559 j) with hm | hm <;> rw [hm] <;> decide
    have e2 : (aStar306559 (5 + 2 * j)).val = (M306559 (2 * j + 2)).val := by
      rw [show (5 + 2 * j : ℕ) = (2 * j + 2) + 3 by omega]
      exact aStar306559_val _
    rw [e2]
    have e3 : (M306559 (2 * j + 2)).val = 1 := congrArg Fin.val (M306559_even_one j)
    omega
  · -- run de bordure : 1 - M(j+1) = M(2j+3)
    show vpos306559 aStar306559 (6 + 2 * j + 1) -
         vpos306559 aStar306559 (6 + 2 * j) - 1 = _
    rw [show (6 + 2 * j + 1 : ℕ) = 5 + 2 * (j + 1) by omega, h61, h52]
    have hc : cum306559 aStar306559 (j + 1 + 3) =
        cum306559 aStar306559 (j + 3) + nlen306559 (M306559 j) := by
      rw [show (j + 1 + 3 : ℕ) = j + 4 by omega]; exact cum_aStar306559 j
    rw [hc]
    have e1 : nlen306559 (M306559 j) - off2306559 (M306559 j) = 1 := by
      rcases fin2_eq_zero_or_one (M306559 j) with hm | hm <;> rw [hm] <;> decide
    have e2 : (aStar306559 (6 + 2 * j)).val = (M306559 (2 * j + 3)).val := by
      rw [show (6 + 2 * j : ℕ) = (2 * j + 3) + 3 by omega]
      exact aStar306559_val _
    rw [e2]
    have e3 : (M306559 (2 * j + 3)).val = 1 - (M306559 (j + 1)).val := by
      have h := M306559_odd_neg (j + 1)
      rwa [show (2 * j + 3 : ℕ) = 2 * (j + 1) + 1 by omega]
    have e4 : off1306559 (M306559 (j + 1)) = 1 - (M306559 (j + 1)).val := by
      rcases fin2_eq_zero_or_one (M306559 (j + 1)) with hm | hm <;>
        rw [hm] <;> decide
    omega

/-! ## (EX) : aStar est point fixe -/

theorem aStar306559_selfdesc : conjectureEX306559 := by
  intro k
  rcases Nat.lt_or_ge k 5 with hk | hk
  · interval_cases k <;> decide
  · obtain ⟨j, hj | hj⟩ : ∃ j : ℕ, k = 5 + 2 * j ∨ k = 6 + 2 * j := by
      exact ⟨(k - 5) / 2, by omega⟩
    · rw [hj]; exact (run_pair306559 j).1
    · rw [hj]; exact (run_pair306559 j).2

/-! ## (UN) : unicite -/

/-- `vpos(k+1)` reste avant `cum(k)` : les voyelles n°1..k+2 vivent dans
    les blocs `0..k-1` (densite 2 par bloc en zone M). -/
theorem vpos_aStar306559_lt_cum (k : ℕ) (hk : 4 ≤ k) :
    vpos306559 aStar306559 (k + 1) < cum306559 aStar306559 k := by
  obtain ⟨j, hj | hj⟩ : ∃ j : ℕ, k + 1 = 5 + 2 * j ∨ k + 1 = 6 + 2 * j := by
    refine ⟨(k + 1 - 5) / 2, by omega⟩
  · rw [hj, (vpos_pair306559 j).1]
    have hle : cum306559 aStar306559 (j + 4) ≤ cum306559 aStar306559 k := by
      apply cum_mono306559; omega
    have hlt : cum306559 aStar306559 (j + 3) + off1306559 (M306559 j) <
        cum306559 aStar306559 (j + 4) := by
      rw [cum_aStar306559]
      have h1 : off1306559 (M306559 j) < nlen306559 (M306559 j) := off1_lt_nlen _
      omega
    omega
  · rw [hj, (vpos_pair306559 j).2]
    have hle : cum306559 aStar306559 (j + 4) ≤ cum306559 aStar306559 k := by
      apply cum_mono306559; omega
    have hlt : cum306559 aStar306559 (j + 3) + off2306559 (M306559 j) <
        cum306559 aStar306559 (j + 4) := by
      rw [cum_aStar306559]
      have h1 : off2306559 (M306559 j) < nlen306559 (M306559 j) := off2_lt_nlen _
      omega
    omega

/-- Les positions `vpos aStar k` portent bien des voyelles. -/
theorem isVowel_vpos306559_aStar (m : ℕ) :
    isVowel306559 (wordOf306559 aStar306559 (vpos306559 aStar306559 m)) = true := by
  rcases Nat.lt_or_ge m 5 with hm | hm
  · interval_cases m <;> decide
  · obtain ⟨j, hj | hj⟩ : ∃ j : ℕ, m = 5 + 2 * j ∨ m = 6 + 2 * j := by
      exact ⟨(m - 5) / 2, by omega⟩
    · rw [hj, (vpos_pair306559 j).1,
          wordOf_eq306559 aStar306559 (j + 3) (off1306559 (M306559 j))
            (by rw [len_aStar306559]; exact off1_lt_nlen _),
          aStar306559_tail]
      exact name_castLE_getD_off1 _ _
    · rw [hj, (vpos_pair306559 j).2,
          wordOf_eq306559 aStar306559 (j + 3) (off2306559 (M306559 j))
            (by rw [len_aStar306559]; exact off2_lt_nlen _),
          aStar306559_tail]
      exact name_castLE_getD_off2 _ _

/-- Accord des positions de voyelles entre `a` et `aStar` tant que les
    noms coincident sur `0..k-1` (densite : les positions scrutees
    restent `< cum(k)`). -/
theorem vpos_congr306559 (a : ℕ → Fin 4) (k : ℕ) (hk : 3 ≤ k)
    (h : ∀ j, j < k → name306559 (a j) = name306559 (aStar306559 j)) :
    ∀ m, m ≤ k + 1 → vpos306559 a m = vpos306559 aStar306559 m := by
  have hw : ∀ i, i < cum306559 aStar306559 k →
      wordOf306559 a i = wordOf306559 aStar306559 i := by
    intro i hi
    obtain ⟨j, r, hit, hij, hrj⟩ := iter_invariant306559 aStar306559 i
    have hjk : j < k := by
      by_contra hc
      push_neg at hc
      have h1 := cum_mono306559 aStar306559 hc
      omega
    have hcum : cum306559 a j = cum306559 aStar306559 j :=
      cum_congr306559 a aStar306559 k j h (by omega)
    have hra : r < (name306559 (a j)).length := by
      have e := congrArg List.length (h j hjk); rw [e]; exact hrj
    have ha : iter306559 (step306559 a) i (0, 0) = (j, r) := by
      rw [hij, ← hcum]; exact iter_at306559 a j r hra
    show (name306559 (a (iter306559 (step306559 a) i (0, 0)).1)).getD
        (iter306559 (step306559 a) i (0, 0)).2 Letter306559.O =
         (name306559 (aStar306559 (iter306559 (step306559 aStar306559) i
          (0, 0)).1)).getD
        (iter306559 (step306559 aStar306559) i (0, 0)).2 Letter306559.O
    rw [ha, hit]
    show (name306559 (a j)).getD r Letter306559.O =
         (name306559 (aStar306559 j)).getD r Letter306559.O
    rw [h j hjk]
  have hbound : vpos306559 aStar306559 (k + 1) < cum306559 aStar306559 k := by
    rcases lt_or_eq_of_le hk with hlt | heq
    · exact vpos_aStar306559_lt_cum k (by omega)
    · subst heq
      show vpos306559 aStar306559 4 < cum306559 aStar306559 3
      have h1 : vpos306559 aStar306559 4 = 10 := by decide
      have h2 : cum306559 aStar306559 3 = 11 := by decide
      omega
  intro m
  induction m with
  | zero =>
      intro _
      show nextVowel306559 a 0 5 = vpos306559 aStar306559 0
      have hv0 : vpos306559 aStar306559 0 = 0 := by decide
      rw [hv0]
      apply nextVowel_agree306559 (b := aStar306559) (d := 0)
      · decide
      · intro i _ h'i; exact absurd h'i (Nat.not_lt_zero i)
      · intro i _ h'i
        apply hw i
        have := hbound; omega
      · decide
  | succ m ih =>
      intro hm
      have hm' : m ≤ k + 1 := by omega
      show nextVowel306559 a (vpos306559 a m + 1) 5 =
           vpos306559 aStar306559 (m + 1)
      rw [ih hm']
      show nextVowel306559 a (vpos306559 aStar306559 m + 1) 5 =
           nextVowel306559 aStar306559 (vpos306559 aStar306559 m + 1) 5
      have hb : vpos306559 aStar306559 (m + 1) < cum306559 aStar306559 k := by
        have hm1 : m + 1 ≤ k + 1 := by omega
        rcases lt_or_eq_of_le hm1 with hlt | heq
        · have h' := vpos_lt_of_lt306559 aStar306559 (m := m + 1) (n := k + 1) hlt
          omega
        · rw [heq]; exact hbound
      have hpd : vpos306559 aStar306559 m + 1 +
          (vpos306559 aStar306559 (m + 1) - (vpos306559 aStar306559 m + 1)) =
          vpos306559 aStar306559 (m + 1) := by
        have := vpos_lt_succ306559 aStar306559 m; omega
      have hA : nextVowel306559 a (vpos306559 aStar306559 m + 1) 5 =
          vpos306559 aStar306559 m + 1 +
          (vpos306559 aStar306559 (m + 1) - (vpos306559 aStar306559 m + 1)) := by
        apply nextVowel_agree306559 (b := aStar306559)
        · rw [hpd]; exact isVowel_vpos306559_aStar _
        · intro i hi h'i
          have hi2 : i < vpos306559 aStar306559 (m + 1) := by
            have := hpd; omega
          exact nextVowel_lt_not_vowel306559 aStar306559
            (vpos306559 aStar306559 m + 1) 5 i hi hi2
        · intro i hi h'i
          apply hw i
          have : i ≤ vpos306559 aStar306559 (m + 1) := by
            have := hpd; omega
          omega
        · have e : vpos306559 aStar306559 (m + 1) -
              (vpos306559 aStar306559 m + 1) = run306559 aStar306559 m := by
            show vpos306559 aStar306559 (m + 1) - (vpos306559 aStar306559 m + 1) =
                 vpos306559 aStar306559 (m + 1) - vpos306559 aStar306559 m - 1
            omega
          rw [e, aStar306559_selfdesc]
          have := (aStar306559 m).isLt; omega
      have hB : nextVowel306559 aStar306559 (vpos306559 aStar306559 m + 1) 5 =
          vpos306559 aStar306559 m + 1 +
          (vpos306559 aStar306559 (m + 1) - (vpos306559 aStar306559 m + 1)) := by
        apply nextVowel_eq306559 aStar306559 _
        · have e : vpos306559 aStar306559 (m + 1) -
              (vpos306559 aStar306559 m + 1) = run306559 aStar306559 m := by
            show vpos306559 aStar306559 (m + 1) - (vpos306559 aStar306559 m + 1) =
                 vpos306559 aStar306559 (m + 1) - vpos306559 aStar306559 m - 1
            omega
          rw [e, aStar306559_selfdesc]
          have := (aStar306559 m).isLt; omega
        · intro i hi h'i
          have hi2 : i < vpos306559 aStar306559 (m + 1) := by
            have := hpd; omega
          exact nextVowel_lt_not_vowel306559 aStar306559
            (vpos306559 aStar306559 m + 1) 5 i hi hi2
        · rw [hpd]; exact isVowel_vpos306559_aStar _
      rw [hA, hB]

theorem aStar306559_unique : conjectureUN306559 := by
  intro a h0 h1 h2 hdesc
  funext k
  induction k using Nat.strongRecOn with
  | ind k ihk =>
      rcases lt_or_ge k 3 with hk | hk
      · interval_cases k
        · exact h0.trans rfl
        · exact h1.trans rfl
        · exact h2.trans rfl
      · -- noms egaux sur 0..k-1 par IH
        have hnames : ∀ j, j < k →
            name306559 (a j) = name306559 (aStar306559 j) := by
          intro j hj; rw [ihk j hj]
        -- runs egaux jusqu'a l'indice k
        have hruns : ∀ m, m ≤ k → run306559 a m = run306559 aStar306559 m := by
          intro m hm
          unfold run306559
          rw [vpos_congr306559 a k hk hnames (m + 1) (by omega),
              vpos_congr306559 a k hk hnames m (by omega)]
        -- conclusion par la valeur du run
        apply Fin.ext
        show (a k).val = (aStar306559 k).val
        rw [← hdesc k, hruns k (le_refl k), aStar306559_selfdesc]

/-- Theoreme principal : existence et unicite du point fixe
    auto-descriptif de A306559 (conjecture Neder). -/
theorem A306559 : conjectureEX306559 ∧ conjectureUN306559 :=
  ⟨aStar306559_selfdesc, aStar306559_unique⟩
