# Theorem Prover for Sentential Logic

Sentential Logic (SL) is a formal language whose logical truths are formally decidable. This means that it's possible to write a program that takes an SL sentence and returns either (1) a proof, or (2) a valuation that makes it false.

That's what this program does.

A valuation is an assignment of a truth value (True or False) to each atomic sentence (i.e. A, B, C, D, ...). A sentence that is True on all valuations is a logical truth. This program uses a natural deduction system to derive logical truths.

The sentence to be assessed is the `sl_sentence` value at the top of `sl.py`.

## Examples:

```
$ python sl.py
(K -> K)
Success!
1.  | ~(K -> K)    Assume
2.  | ~(~K v K)    -> exch. 1
3.  | (~~K & ~K)    De Morgan's 2
4.  | (K & ~K)    ~~ elim. 3
5.  | K    & elim 4
6.  | ~K    & elim 4
7.  | (K & ~K)    & intro. 5, 6
8.  (~(K -> K) -> (K & ~K))    -> intro. 1, 7
9.  (K -> K)    ~ elim. 8
```

```
$ python sl.py
(A v (~B v C))
Counterexample found:
    A: False
    B: True
    C: False
```
