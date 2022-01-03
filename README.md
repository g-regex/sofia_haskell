# Sofia/Haskell

This project aims to create a Haskell version of the [Sofia](https://github.com/ZurabJanelidze/sofia) proof assistant. It is work in progress.

## Usage

To use the proof assistant, load the `Sofia.hs` in `ghci`. Then use the proof building functions to build up proofs. Each proof building function creates a new `Proof` (i.e. a list of `ProofLine`s) from a previous one. Hence the previous `Proof` is given as the last parameter to each proof building function. `newProof` is the empty list of `ProofLine`s and can be used as the predecessor of a `Proof` that is newly built up.

Here is an example of how to type out a proof of Russel's paradox:

```haskell
ex8_1 = assume "[X][[x]:[[[x] in [X]]=[[[x] in [x]]:[False[]]]]]" newProof
ex8_2 = apply 1 [(1,1)] 2 ex8_1
ex8_3 = assume "[[X] in [X]]" ex8_2
ex8_4 = rightsub 2 3 [1..] 1 1 ex8_3
ex8_5 = apply 4 [] 1 ex8_4
ex8_6 = synapsis ex8_5
ex8_7 = leftsub 2 6 [1..] 1 1 ex8_6
ex8_8 = apply 6 [] 1 ex8_7
ex8_9 = synapsis ex8_8
```

