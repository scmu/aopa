# Algebra of Programming in Agda: Dependent Types for Relational Program Derivation

The AoPA library allows one to encode [Algebra of Programming (BdM97)][BdM97] style program derivation, both functional and relational, in Agda.

Since the 90s, the program derivation community has been exploring moving from functions to a relational theory of program calculation, culminating in the work of [Bird and de Moor][BdM97]. A problem is specified as a relation that maps inputs to outputs, which allows us not to be over specific about which output to choose when they are equally good, leaving the choices to implementations. The task is to refine the specification into a functional implementation, using algebraic properties.

Meanwhile, the programming language community has been moving toward more reliance on machine-aided program verification. Complex theorems are considered "proved" only if the proof is verified by a theorem prover or a proof assistant.

AoPA allows us to  to develop relational proofs, in Agda,  in the style of Bird and de Moor. Elements of the relational theory of programs are modelled in the type system of Agda. Calculations are expressed as program terms that, if type-checked, is guaranteed to be correct. In the end of a calculation one may extract a functional program that is proved to respect the relational specification.

## Quick Example

The following is a derivation of insertion sort in progress:

```
isort-der : ∃ (\f → ordered? ○ permute ⊒ fun f )
isort-der = (_ , (
  ⊒-begin
      ordered? ○ permute
  ⊒⟨ (\vs -> ·-monotonic ordered? (permute-is-fold vs)) ⟩
      ordered? ○ foldR combine nil
  ⊒⟨ foldR-fusion ordered? ins-step ins-base ⟩
      foldR (fun (uncurry insert)) nil
  ⊒⟨ { foldR-to-foldr insert []}0 ⟩
      { fun (foldr insert [])
  ⊒∎ }1))

isort : [ Val ] -> [ Val ]
isort = proj₁ isort-der
```

The type of `isort-der` is a proposition that there exists a function `f` that is contained in `ordered ? ◦ permute`, a relation mapping a list to one of its ordered permutations. The proof proceeds by derivation from the specification towards the algorithm. The first step exploits monotonicity of `◦` and that permute can be expressed as a fold. The second step makes use of relational fold fusion. The shaded areas denote interaction points -- fragments of (proof) code to be completed. The programmer can query Agda for the expected type and the context of the shaded expression. When the proof is completed, an algorithm `isort` is obtained by extracting the witness of the proposition. It is an executable program that is backed by the type system to meet the specification.

The complete program is in the Example directory of the code.

## Files

The library currently consists of the following folders:


* `Relations`: modules defining various relational operators and their properties. These include relational factors, minimum and maximum, monotype factor, Galois connections, and the "shrink" operator of Oliveira [(MO11)][MO11].

* `AlgebraicReasoning`: a number of modules supporting algebraic reasoning. We are in the progress of integrating this with the `PreorderReasoning` module in the Agda Standard Library.

* `Data`: defining relational fold, unfold, hylomorphism (using well-founded recursion), the greedy theorem, and the converse-of-a-function theorem, etc, for lists, binary trees, and generic datatypes using polynomial base functors.

* `Examples`: currently we have prepared four examples: a functional derivation of the maximum segment sum problem, a relational derivation of insertion sort and quicksort (following the paper Functional Algorithm Design by Richard Bird), and solving an optimisation problem using the greedy theorem.




## History

The earliest version of AoPA was developed by Shin-Cheng Mu, Hsiang-Shang Ko, and Patrik Jansson, accompanying their papers [(MKJ08)][MKJ08] [(MKJ09)][MKJ09]. The development is currently picked up by Yu-Hsi Chiang and Shin-Cheng Mu. New additions include universe polymorphism, generic datatypes with polymorphic base functors, and theories for developing algorithms from Galois connections [(MO11)][MO11] [(CM15)][CM15].

## References

* [(BdM97)][BdM97] Richard Bird and Oege de Moor, [Algebra of Programming][BdM97]. Prentice Hall, 1997.

* [(MKJ08)][MKJ08] Shin-Cheng Mu, Hsiang-Shang Ko, and Patrik Jansson, [Algebra of Programming Using Dependent Types][MKJ08]. Mathematics of Program Construction, LNCS 5133, pp 268-283, 2008.

* [(MKJ09)][MKJ09] Shin-cheng Mu, Hsiang-shang Ko, and Patrik Jansson, [Algebra of programming in Agda: Dependent types for relational program derivation][MKJ09]. Journal of Functional Programming, Volume 19 Issue 5, September 2009, pp 545-579. doi>[10.1017/S0956796809007345](http://dx.doi.org/10.1017/S0956796809007345).

* [(MO11)][MO11] Shin-Cheng Mu and José Nuno Oliveira, [Programming from Galois connections][MO11]. The Journal of Logic and Algebraic Programming, Volume 81, Issue 6, August 2012, pp 680–704. doi>[10.1016/j.jlap.2012.05.003](http://dx.doi.org/10.1016/j.jlap.2012.05.003).

* [(CM15)][CM15] Yu-Hsi Chiang and Shin-Cheng Mu, [Formal derivation of greedy algorithms from relational specifications: A tutorial][CM15]. Journal of Logical and Algebraic Methods in Programming. In Press.


[BdM97]: http://www.amazon.com/Algebra-Programming-Prentice-Hall-International-Computer/dp/013507245X

[MKJ08]: http://link.springer.com/chapter/10.1007%2F978-3-540-70594-9_15#page-1

[MKJ09]: http://dl.acm.org/citation.cfm?id=1630627 "Algebra of programming in Agda: Dependent types for relational program derivation"

[MO11]: http://www.sciencedirect.com/science/article/pii/S1567832612000525

[CM15]: http://www.sciencedirect.com/science/article/pii/S2352220815001492
