WIP project to translate proofs from a Dedukti encoding of Predicate logic to the tactics language of proofs assistants. 

# Installation

The project requires [Dedukti](https://github.com/deducteam/dedukti) and is built with `dune`.

```makefile
git clone https://gitlab.crans.org/geran/dkpltact.git
cd dkpltact
dune build
```

# Usage

The command `dune execk dkpltact <folder>` translates the dedukti files of `<folder>` in Coq and writes the results in the folder `output`.


## Encoding

The files should be written following the encoding of
[`input/plth.dk`](./input/plth.dk). Some useful terms
(to introduce and eliminate connectives) are given in [`input/logic.dk`](./input/logic.dk).

The encoding permits to declare sets, predicates, functions, and elements of sets (so functions of arity 0), hence the signature of the theory that one wants to encode.
```dedukti
nat: plth.Set.
0: plth.El nat.
s: plth.function (plth.cons nat plth.nil) nat.
plus: plth.function (plth.cons nat (plth.cons nat plth.nil)) nat.
even: plth.predicate (plth.cons nat plth.nil).
zero?: plth.predicate (plth.cons nat plth.nil).
```

Besides, we can also declare proofs, which means states an axiom.
```dedukti
zero?_0: plth.Prf (zero? 0).
zero?_s: plth.Prf (plth.forall nat (n: plth.El nat =>
  plth.not (zero? (s n))
)).

even_0: plth.Prf (even 0).
even_s: plth.Prf (plth.forall nat (n: plth.El nat => 
  plth.imp (even n) (even (s (s n)))
)).

not_even_1: plth.Prf (plth.not (even (s 0))).
not_even_s: plth.Prf (plth.forall nat (n: plth.El nat => 
  plth.imp (plth.not (even n)) (plth.not (even (s (s n))))
)).

plus_0: plth.Prf (plth.forall nat (n: plth.El nat => 
  plth.eq nat (plus n 0) n
)).

plus_s: plth.Prf (plth.forall nat (n: plth.El nat => 
  plth.forall nat (m: plth.El nat => 
    plth.eq nat (plus n (s m)) (s (plus n m)))  
)).
```

Then we can define elements, functions, predicates and proof,
and thus we can prove propositions.
```dedukti
def 1: plth.El nat := s 0.

def successor?: plth.predicate (plth.cons nat plth.nil) :=
  (n: plth.El nat => plth.not (zero? n)).

def twice: plth.function (plth.cons nat plth.nil) nat :=
  (n: plth.El nat => plus n n). 

thm even_2: plth.Prf (even (s (s 0))) := 
  even_s 0 even_0.

thm even_2_plus_0: plth.Prf (even (plus (s (s 0)) 0)) :=
  logic.eq_ind_r nat (s (s 0)) (n: plth.El nat => even n) even_2  (plus (s (s 0)) 0) (plus_0 (s (s 0))). 
```

The above proofs are easy to write. To write more complex proofs, [`input/logic.dk`](./input/logic.dk) provides terms to introduce and eliminate the connectives (`logic.eq_ind_r` is one of them). 

### Classical logic

The encoding has two ways to build classic proofs. First, with the term `plth.classic` which takes a proposition `p` and gives a proof of `plth.or p (plth.not p)` (excluded-middle), and with the term `plth.nnpp` which takes a proposition `p` and gives a proof of `plth.imp (plth.not (plth.not p)) p` (double negation elimination). 

## Examples

The proofs of Euclid Book I are given in [`input/euclid`](./input/euclid). 
