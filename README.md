# First order logic in Coq

Here, Coq acts as the meta-logic. Since Coq is very powerful, we can easily
prove a lot of meta-theorems.

We feature a Hilbert style system, with two inference rules: _modus ponens_
and _universal generalization_. If `P` is deducible from premises `G` with
the two rules only, we write `G |-0 P`.

Next, we define `G |-c P` as "`P` is provable from `G` and some set of axioms
instantiated from axiom schemas". For instance, `[] |-c P --> Q --> P`, since
`P --> Q --> P` is provable from `[]` and the axioms `[P --> Q --> P]`, where
the axiom is instantiated from axiom (schema) K.

We provide a small but handy set of tactics to automate the reasoning on
lists that is frequently required when proving results.

Every meta-theorem about `|-0` (e.g. weakening and contraction) can be lifted
to a meta-theorem about `|-c`; every meta-theorem about `|-c` (e.g.
`|-c P --> Q` implies `|-c ¬Q --> ¬P`) can be lifted to a meta-theorem with
an antecedent attached in each sequent (e.g. `|-c A --> (P --> Q)` implies
`|-c A --> (¬Q --> ¬P)`). They will have the name `foo`, `foo_c`, `foo_d`,
correspondingly. The latter lift is the essence of **deduction theorem**,
which is also included in our Coq file.

Next, we will prove some useful results on other derived logical connectives,
and get ready to dive into some concrete theories!
