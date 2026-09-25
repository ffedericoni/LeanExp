"""Traduttore Python → MiniPy (l'AST Lean definito in LeanExp/Passo3_MiniPython.lean).

Uso:
    python3 tools/py2lean.py python/esempi.py -o LeanExp/Generato/Esempi.lean
    python3 tools/py2lean.py python/esempi.py --check -o LeanExp/Generato/Esempi.lean

Per ogni funzione del file prova a tradurre il corpo in un `MiniPy.Stmt`.
Le funzioni che usano costrutti fuori dal frammento supportato vengono
saltate, e il motivo viene scritto come commento nel file generato.

Frammento supportato (tutto il resto viene rifiutato con un errore esplicito):
  * espressioni: costanti intere, variabili, `+`, `-`, `*`, `-x` unario
  * condizioni:  `<`, `<=`, `>`, `>=`, `==`, `!=`, `and`, `or`, `not`
  * istruzioni:  `x = e`, `x += e`, `x -= e`, `x *= e`, `if`/`elif`/`else`,
                 `while` (senza `else`), `pass`
  * `return x` solo come ultima istruzione della funzione, e solo di una variabile

Il principio guida è: **meglio rifiutare che tradurre male**. Ogni costrutto
accettato ha, in MiniPy, esattamente il significato che ha in Python.
"""

from __future__ import annotations

import argparse
import ast
import sys
from dataclasses import dataclass


class NonSupportato(Exception):
    """Costrutto Python che non sappiamo tradurre fedelmente."""

    def __init__(self, nodo: ast.AST, motivo: str):
        riga = getattr(nodo, "lineno", "?")
        super().__init__(f"riga {riga}: {motivo}")


@dataclass
class Traduzione:
    nome: str
    parametri: list[str]
    risultato: str
    corpo: str  # termine Lean di tipo MiniPy.Stmt


# --- Espressioni --------------------------------------------------------------

def lean_int(n: int) -> str:
    return f"({n})" if n < 0 else str(n)


def espr(e: ast.expr) -> str:
    match e:
        case ast.Constant(value=bool()):
            raise NonSupportato(e, "i booleani non sono interi in MiniPy")
        case ast.Constant(value=int() as n):
            return f"(.cost {lean_int(n)})"
        case ast.Name(id=x):
            return f'(.var "{x}")'
        case ast.BinOp(left=a, op=op, right=b):
            ctor = {ast.Add: "add", ast.Sub: "sub", ast.Mult: "mul"}.get(type(op))
            if ctor is None:
                raise NonSupportato(e, f"operatore {type(op).__name__} non supportato "
                                       "(es. `//` e `%` in Python arrotondano diversamente da Lean)")
            return f"(.{ctor} {espr(a)} {espr(b)})"
        case ast.UnaryOp(op=ast.USub(), operand=a):
            return f"(.sub (.cost 0) {espr(a)})"
        case _:
            raise NonSupportato(e, f"espressione {type(e).__name__} non supportata")


def cond(c: ast.expr) -> str:
    match c:
        case ast.Compare(left=a, ops=[op], comparators=[b]):
            ea, eb = espr(a), espr(b)
            match op:
                case ast.Lt():    return f"(.lt {ea} {eb})"
                case ast.Gt():    return f"(.lt {eb} {ea})"
                case ast.LtE():   return f"(.not (.lt {eb} {ea}))"
                case ast.GtE():   return f"(.not (.lt {ea} {eb}))"
                case ast.Eq():    return f"(.eq {ea} {eb})"
                case ast.NotEq(): return f"(.not (.eq {ea} {eb}))"
            raise NonSupportato(c, f"confronto {type(op).__name__} non supportato")
        case ast.Compare():
            raise NonSupportato(c, "confronti concatenati (a < b < c) non supportati")
        case ast.BoolOp(op=op, values=vs):
            ctor = "and" if isinstance(op, ast.And) else "or"
            risultato = cond(vs[-1])
            for v in reversed(vs[:-1]):
                risultato = f"(.{ctor} {cond(v)} {risultato})"
            return risultato
        case ast.UnaryOp(op=ast.Not(), operand=a):
            return f"(.not {cond(a)})"
        case _:
            # es. `while x:` — in Python usa la "truthiness" di x: rifiutiamo
            raise NonSupportato(c, "la condizione deve essere un confronto esplicito")


# --- Istruzioni ---------------------------------------------------------------

def indenta(s: str, n: int = 2) -> str:
    return "\n".join(" " * n + riga for riga in s.splitlines())


def blocco(stmts: list[ast.stmt]) -> str:
    """Una sequenza di istruzioni, annidata a destra: seq s₁ (seq s₂ s₃)."""
    tradotte = [istr(s) for s in stmts]
    risultato = tradotte[-1]
    for t in reversed(tradotte[:-1]):
        risultato = f"(.seq\n{indenta(t)}\n{indenta(risultato)})"
    return risultato


def bersaglio(t: ast.expr) -> str:
    if not isinstance(t, ast.Name):
        raise NonSupportato(t, "si può assegnare solo a una variabile semplice")
    return t.id


def istr(s: ast.stmt) -> str:
    match s:
        case ast.Assign(targets=[t], value=v):
            return f'(.assign "{bersaglio(t)}" {espr(v)})'
        case ast.Assign():
            raise NonSupportato(s, "assegnamenti multipli (a = b = e) non supportati")
        case ast.AugAssign(target=t, op=op, value=v):
            x = bersaglio(t)
            fittizio = ast.BinOp(left=ast.Name(id=x), op=op, right=v, lineno=s.lineno)
            return f'(.assign "{x}" {espr(fittizio)})'
        case ast.If(test=c, body=b, orelse=o):
            altrimenti = blocco(o) if o else ".pass"
            return f"(.ite {cond(c)}\n{indenta(blocco(b))}\n{indenta(altrimenti)})"
        case ast.While(orelse=[_, *_]):
            raise NonSupportato(s, "`while ... else` non supportato")
        case ast.While(test=c, body=b):
            return f"(.while {cond(c)}\n{indenta(blocco(b))})"
        case ast.Pass():
            return ".pass"
        case ast.Return():
            raise NonSupportato(s, "`return` ammesso solo come ultima istruzione")
        case _:
            raise NonSupportato(s, f"istruzione {type(s).__name__} non supportata")


# --- Controllo delle variabili ------------------------------------------------

def controlla_variabili(f: ast.FunctionDef, parametri: list[str]) -> None:
    """In MiniPy una variabile mai assegnata ha un valore (quello dello stato
    iniziale), in Python dà `NameError`. Richiediamo quindi che ogni variabile
    letta sia un parametro o venga assegnata *prima* nel corpo (controllo
    conservativo: un assegnamento dentro un `if` o un `while` non conta per
    le istruzioni successive, perché potrebbe non essere eseguito)."""

    def letture(n: ast.AST) -> list[ast.Name]:
        return [x for x in ast.walk(n) if isinstance(x, ast.Name)]

    def visita(stmts: list[ast.stmt], definite: set[str]) -> set[str]:
        definite = set(definite)
        for s in stmts:
            match s:
                case ast.Assign(targets=[t], value=v):
                    controlla(letture(v), definite)
                    definite.add(bersaglio(t))
                case ast.AugAssign(target=t, value=v):
                    controlla(letture(t) + letture(v), definite)
                case ast.If(test=c, body=b, orelse=o):
                    controlla(letture(c), definite)
                    definite |= visita(b, definite) & visita(o, definite)
                case ast.While(test=c, body=b):
                    controlla(letture(c), definite)
                    visita(b, definite)
                case ast.Return(value=v) if v is not None:
                    controlla(letture(v), definite)
        return definite

    def controlla(nomi: list[ast.Name], definite: set[str]) -> None:
        for n in nomi:
            if n.id not in definite:
                raise NonSupportato(n, f"variabile `{n.id}` forse non definita")

    visita(f.body, set(parametri))


# --- Funzioni -----------------------------------------------------------------

def traduci_funzione(f: ast.FunctionDef) -> Traduzione:
    a = f.args
    if a.vararg or a.kwarg or a.kwonlyargs or a.posonlyargs or a.defaults:
        raise NonSupportato(f, "solo parametri posizionali semplici")
    parametri = [p.arg for p in a.args]
    for p in a.args:
        if not (isinstance(p.annotation, ast.Name) and p.annotation.id == "int"):
            raise NonSupportato(p, f"il parametro `{p.arg}` deve essere annotato `int`")

    corpo = list(f.body)
    # salta la docstring
    if corpo and isinstance(corpo[0], ast.Expr) and isinstance(corpo[0].value, ast.Constant):
        corpo = corpo[1:]
    match corpo:
        case [*prima, ast.Return(value=ast.Name(id=r))] if prima:
            pass
        case _:
            raise NonSupportato(f, "il corpo deve terminare con `return <variabile>`")

    controlla_variabili(f, parametri)
    return Traduzione(f.name, parametri, r, blocco(prima))


def genera(sorgente: str, nome_file: str, modulo: str) -> str:
    albero = ast.parse(sorgente, nome_file)
    righe = [
        "import LeanExp.Passo3_MiniPython",
        "",
        "/-! File GENERATO da tools/py2lean.py — non modificare a mano.",
        f"Sorgente: `{nome_file}` -/",
        "",
        f"namespace Generato.{modulo}",
        "open MiniPy",
        "",
    ]
    for f in albero.body:
        if not isinstance(f, ast.FunctionDef):
            continue
        try:
            t = traduci_funzione(f)
        except NonSupportato as err:
            righe += [f"-- `{f.name}` non tradotta: {err}", ""]
            continue
        righe += [
            f"/-- `{t.nome}` ({nome_file}, riga {f.lineno}).",
            f"Parametri: {', '.join(t.parametri) or 'nessuno'}; risultato nella variabile `{t.risultato}`. -/",
            f"def {t.nome} : Stmt :=",
            indenta(t.corpo),
            "",
            f'def {t.nome}.parametri : List String := [{", ".join(f"{chr(34)}{p}{chr(34)}" for p in t.parametri)}]',
            f'def {t.nome}.risultato : String := "{t.risultato}"',
            "",
        ]
    righe += [f"end Generato.{modulo}", ""]
    return "\n".join(righe)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("sorgente")
    ap.add_argument("-o", "--output", required=True)
    ap.add_argument("--modulo", default=None, help="nome del namespace Lean")
    ap.add_argument("--check", action="store_true",
                    help="non scrive nulla: fallisce se il file generato non è aggiornato")
    args = ap.parse_args()

    with open(args.sorgente) as fh:
        sorgente = fh.read()
    modulo = args.modulo or args.output.rsplit("/", 1)[-1].removesuffix(".lean")
    testo = genera(sorgente, args.sorgente, modulo)

    if args.check:
        try:
            with open(args.output) as fh:
                attuale = fh.read()
        except FileNotFoundError:
            attuale = None
        if attuale != testo:
            print(f"{args.output} non è aggiornato: rigenera con py2lean.py", file=sys.stderr)
            return 1
        return 0

    with open(args.output, "w") as fh:
        fh.write(testo)
    return 0


if __name__ == "__main__":
    sys.exit(main())
