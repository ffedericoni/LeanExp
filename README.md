# LeanExp — Dimostrare la correttezza di programmi Python con Lean 4

Percorso a passi incrementali. Ogni file Lean corrisponde a funzioni di
[`python/esempi.py`](python/esempi.py).

| Passo | File | Idea | Cosa si impara |
|---|---|---|---|
| 1 | [`Passo1_Shallow.lean`](LeanExp/Passo1_Shallow.lean) | *Shallow embedding*: si traduce a mano la funzione Python in una funzione Lean pura | `for` → `foldl`, invarianti come lemmi generalizzati, induzione su liste, precondizioni nei tipi |
| 2 | [`Passo2_Cicli.lean`](LeanExp/Passo2_Cicli.lean) | Cicli `while` come ricorsione | terminazione (`termination_by`), induzione funzionale, invarianti, attenzione a `int` vs `Nat` |
| 3 | [`Passo3_MiniPython.lean`](LeanExp/Passo3_MiniPython.lean) | *Deep embedding*: sintassi + semantica di un mini-Python in Lean | semantica big-step, regola di Hoare per il `while` dimostrata una volta sola, interprete eseguibile dimostrato corretto |

## Come compilare

```bash
# installa Lean (una volta sola)
curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y
lake build          # verifica tutte le dimostrazioni
python3 python/esempi.py
```

Se `lake build` termina senza errori, **tutti i teoremi sono dimostrati**
(non ci sono `sorry`). Si consiglia VS Code con l'estensione *Lean 4* per
vedere lo stato della dimostrazione passo passo.

## Il punto critico: il divario Python ↔ Lean

Lean dimostra teoremi sul **modello**, non sul file `.py`. Le fonti di errore
sono nella traduzione:

* `int` di Python è illimitato → usare `Int`, non `Nat` né `Int64`
  (vedi Passo 2: con `Nat` `somma_fino_a(-3)` sparirebbe dal teorema);
* aliasing e mutabilità delle liste, eccezioni (`IndexError`), `None`,
  tipizzazione dinamica: nei passi 1–2 vengono semplicemente ignorati;
* nel passo 3 il divario si riduce a *una* cosa di cui fidarsi, la
  semantica di `MiniPy`, invece che a ogni traduzione manuale.

## Possibili prossimi passi

1. **Traduttore automatico** Python → `MiniPy.Stmt` scritto in Python con il
   modulo `ast`, che genera il file Lean dell'AST.
2. **Test differenziali**: eseguire `MiniPy.run` e Python sugli stessi input
   (anche con Hypothesis) per acquisire fiducia nella semantica.
3. Estendere `MiniPy` con liste, funzioni, `return`, eccezioni.
4. Un *verification condition generator*: calcolare automaticamente le
   obbligazioni di prova dalle annotazioni (`assert`, invarianti) come fanno
   Dafny o Nagini (il verificatore per Python basato su Viper).
