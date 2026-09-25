/-!
# Passo 1 — "Shallow embedding": tradurre Python in Lean a mano

L'idea più semplice: riscriviamo ogni funzione Python come funzione Lean
*pura*, restando il più possibile fedeli alla struttura del codice originale,
e poi dimostriamo che rispetta una specifica.

Scelte di traduzione (da tenere a mente, sono il punto debole del metodo):
* `int` di Python è illimitato → `Int` di Lean (non `Int64`!).
* `list[int]` → `List Int`.
* un ciclo `for` con accumulatore → `List.foldl`.
* un `return` anticipato dentro un ciclo → ricorsione strutturale.

Il file Python di riferimento è `python/esempi.py`.
-/

namespace Passo1

/-! ## `somma`

```python
def somma(xs):
    tot = 0
    for x in xs:
        tot += x
    return tot
```
-/

/-- Traduzione fedele: il ciclo `for` con accumulatore `tot` è un `foldl`. -/
def somma (xs : List Int) : Int :=
  xs.foldl (fun tot x => tot + x) 0

/-- Specifica: la definizione matematica "ovvia" di somma (ricorsiva). -/
def sommaSpec : List Int → Int
  | [] => 0
  | x :: xs => x + sommaSpec xs

-- Possiamo eseguire il modello, come faremmo con Python:
#eval somma [1, 2, 3]   -- 6

/-- Lemma chiave (è l'invariante del ciclo!): partendo da un accumulatore
`acc`, il ciclo restituisce `acc + somma degli elementi rimanenti`. -/
theorem foldl_somma (acc : Int) (xs : List Int) :
    xs.foldl (fun tot x => tot + x) acc = acc + sommaSpec xs := by
  induction xs generalizing acc with
  | nil => simp [sommaSpec]
  | cons x xs ih => simp [sommaSpec, ih]; omega

/-- Correttezza: il programma calcola la specifica. -/
theorem somma_corretta (xs : List Int) : somma xs = sommaSpec xs := by
  simp [somma, foldl_somma]

/-- Una proprietà in più, derivata dalla specifica. -/
theorem somma_append (xs ys : List Int) :
    somma (xs ++ ys) = somma xs + somma ys := by
  simp only [somma_corretta]
  induction xs with
  | nil => simp [sommaSpec]
  | cons x xs ih => simp [sommaSpec, ih]; omega

/-! ## `massimo`

```python
def massimo(xs):          # precondizione: xs non vuota
    m = xs[0]
    for x in xs[1:]:
        if x > m:
            m = x
    return m
```

La precondizione "lista non vuota" la codifichiamo nel *tipo*: la funzione
riceve il primo elemento `x` e il resto `xs` separatamente, quindi è
impossibile chiamarla su una lista vuota.
-/

/-- Il corpo del ciclo: un passo di aggiornamento di `m`. -/
def passoMax (m y : Int) : Int := if y > m then y else m

def massimo (x : Int) (xs : List Int) : Int :=
  xs.foldl passoMax x

/-- Invariante del ciclo (1): il valore corrente `m` non diminuisce mai, e
alla fine è ≥ di tutti gli elementi visitati. -/
theorem massimo_ge (m : Int) (xs : List Int) :
    m ≤ xs.foldl passoMax m ∧ ∀ y ∈ xs, y ≤ xs.foldl passoMax m := by
  induction xs generalizing m with
  | nil => simp
  | cons y ys ih =>
    simp only [List.foldl_cons, List.mem_cons, forall_eq_or_imp]
    -- due casi, come l'`if` nel corpo del ciclo
    by_cases hy : y > m
    · have ⟨h1, h2⟩ := ih y
      simp only [passoMax, hy, ite_true]
      exact ⟨by omega, h1, h2⟩
    · have ⟨h1, h2⟩ := ih m
      simp only [passoMax, hy, ite_false]
      exact ⟨h1, by omega, h2⟩

/-- Invariante del ciclo (2): `m` è sempre uno degli elementi della lista. -/
theorem massimo_mem (m : Int) (xs : List Int) :
    xs.foldl passoMax m ∈ m :: xs := by
  induction xs generalizing m with
  | nil => simp
  | cons y ys ih =>
    simp only [List.foldl_cons, List.mem_cons]
    by_cases hy : y > m
    · simp only [passoMax, hy, ite_true]
      rcases List.mem_cons.mp (ih y) with h | h <;> simp [h]
    · simp only [passoMax, hy, ite_false]
      rcases List.mem_cons.mp (ih m) with h | h <;> simp [h]

/-- Correttezza di `massimo`: restituisce un elemento della lista che è
maggiore o uguale a tutti gli altri. -/
theorem massimo_corretto (x : Int) (xs : List Int) :
    massimo x xs ∈ x :: xs ∧ ∀ y ∈ x :: xs, y ≤ massimo x xs := by
  have ⟨h1, h2⟩ := massimo_ge x xs
  exact ⟨massimo_mem x xs, by simpa [massimo, h1] using h2⟩

/-! ## `contiene` (con `return` anticipato)

```python
def contiene(xs, y):
    for x in xs:
        if x == y:
            return True
    return False
```
-/

def contiene (xs : List Int) (y : Int) : Bool :=
  match xs with
  | [] => false
  | x :: rest => if x == y then true else contiene rest y

theorem contiene_corretto (xs : List Int) (y : Int) :
    contiene xs y = true ↔ y ∈ xs := by
  induction xs with
  | nil => simp [contiene]
  | cons x rest ih =>
    by_cases h : x = y
    · simp [contiene, h]
    · simp [contiene, h, ih, Ne.symm h]

end Passo1
