/-!
# Passo 2 — Cicli `while`: terminazione e invarianti

```python
def somma_fino_a(n):
    i = 0
    tot = 0
    while i < n:
        i += 1
        tot += i
    return tot
```

Un ciclo `while` diventa una funzione ricorsiva i cui parametri sono le
variabili modificate dal ciclo (`i`, `tot`). Lean pretende che ogni funzione
termini: dobbiamo fornire una *misura* che decresce a ogni iterazione
(`termination_by`). Qui è `n - i`, esattamente il "variant" che useremmo
in una dimostrazione su carta.

Nota di fedeltà: `n` in Python può essere negativo! Per questo usiamo `Int`
e non `Nat`: con `Nat` avremmo dimostrato un teorema su un programma
diverso da quello reale.
-/

namespace Passo2

/-- Il ciclo `while`: una iterazione per chiamata ricorsiva. -/
def ciclo (n i tot : Int) : Int :=
  if i < n then ciclo n (i + 1) (tot + (i + 1)) else tot
termination_by (n - i).toNat

/-- La funzione completa: inizializzazione + ciclo. -/
def sommaFinoA (n : Int) : Int := ciclo n 0 0

#eval sommaFinoA 10   -- 55
#eval sommaFinoA (-3) -- 0

/-- **Invariante del ciclo**: `2 * tot = i * (i + 1)` e `0 ≤ i ≤ n`.
Se vale all'ingresso, all'uscita (`i = n`) otteniamo la formula di Gauss.

La dimostrazione procede per *induzione funzionale* su `ciclo`: Lean genera
un caso per ogni ramo dell'`if`, esattamente come nella regola di Hoare
per il `while`. -/
theorem ciclo_invariante (n i tot : Int)
    (h0 : 0 ≤ i) (hin : i ≤ n) (hinv : 2 * tot = i * (i + 1)) :
    2 * ciclo n i tot = n * (n + 1) := by
  fun_induction ciclo n i tot with
  | case1 i tot hlt ih =>
    -- corpo del ciclo: l'invariante si preserva
    apply ih (by omega) (by omega)
    grind
  | case2 i tot hge =>
    -- uscita dal ciclo: ¬(i < n) e i ≤ n ⇒ i = n
    have : i = n := by omega
    subst this; exact hinv

/-- Correttezza per `n ≥ 0`: la formula di Gauss. -/
theorem sommaFinoA_corretta (n : Int) (hn : 0 ≤ n) :
    2 * sommaFinoA n = n * (n + 1) :=
  ciclo_invariante n 0 0 (by omega) hn (by omega)

/-- Comportamento per `n < 0`: il ciclo non viene mai eseguito. -/
theorem sommaFinoA_negativo (n : Int) (hn : n < 0) : sommaFinoA n = 0 := by
  unfold sommaFinoA
  rw [ciclo]
  simp [show ¬ (0 < n) by omega]

end Passo2
