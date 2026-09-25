"""Programmi Python di cui dimostriamo la correttezza in Lean.

Ogni funzione ha un modello corrispondente in LeanExp/*.lean.
"""


# --- Passo 1: cicli `for` su liste -------------------------------------------

def somma(xs: list[int]) -> int:
    tot = 0
    for x in xs:
        tot += x
    return tot


def massimo(xs: list[int]) -> int:
    """Precondizione: xs non vuota."""
    m = xs[0]
    for x in xs[1:]:
        if x > m:
            m = x
    return m


def contiene(xs: list[int], y: int) -> bool:
    for x in xs:
        if x == y:
            return True
    return False


# --- Passo 2 e 3: ciclo `while` con invariante -------------------------------

def somma_fino_a(n: int) -> int:
    i = 0
    tot = 0
    while i < n:
        i += 1
        tot += i
    return tot


if __name__ == "__main__":
    assert somma([1, 2, 3]) == 6
    assert massimo([3, 7, 2]) == 7
    assert contiene([1, 2, 3], 2) and not contiene([1, 2, 3], 5)
    assert somma_fino_a(10) == 55 and somma_fino_a(-3) == 0
    print("ok")
