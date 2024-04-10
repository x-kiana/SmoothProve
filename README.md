# SmoothProve
The smoothest prover ever. Will Prolog loop and fail? Will it Prove Like Butter?™️
## The logic and theory
Our theorem prover (turned proof assistant) is written specifically for the judgemental first-order Zermelo-Fraenkel set theory (i.e., our system is built using the axioms of the Zermelo-Fraenkel set theory, we use first-order logic, and we have judgements that we will explain later)! This specific logic is used in the [CPSC509](https://www.cs.ubc.ca/~rxg/cpsc509-spring-2024/) course at UBC which is how we learnt about it.
### What are judgements?
In our logic, like others, we have propositions. Judgements are claims about propositions and set expressions that we can prove. Here, we have 4 of them.
* Judgement that a set expression describes a valid set
* Judgement that a proposition is well-formed
* Judgement that we can use a proposition
* Judgement that we can verif a proposition
### How do we prove things?
In JZF, proofs are derivation trees that follow the rules described in order to prove a specific judgement about a proposition or set expression.
