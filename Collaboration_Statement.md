# Collaboration statement

## Planning

Before writing any Lean, we met to outline how we wanted to tackle the project as a whole. We talked through what the main result should be (the Boltzmann distribution maximizes entropy and minimizes free energy) and which supporting pieces we would need to get there. From that discussion we outlined the structure of the project together: `Defs.lean`, `Variational.lean`, `Gibbs.lean`, `Limits.lean`, `Examples.lean` and `Main.lean`. Once we agreed on which definitions, lemmas and theorems each file would need, Yuktha wrote up an outline of the statements (with `sorry`s) so that we both had something concrete to work from.

## `Defs.lean`, `Examples.lean`, `Variational.lean`, `Gibbs.lean`

Yuktha started by writing `Defs.lean`, which covers the definitions of a probability distribution and the Boltzmann distribution, and the proof that the Boltzmann distribution is a valid probability distribution. Yuktha also did the proofs in `Variational.lean` and wrote `Examples.lean`, using examples we picked out together from physics textbooks. Yuktha then started on `Gibbs.lean`, and Cassandra took over from there and finished the bulk of the proofs (Gibbs' inequality and its consequences). Later on, Yuktha went back and updated `Defs.lean` based on feedback from our TA.

## `Main.lean`, `Limits.lean`

After `Gibbs.lean` was done, Yuktha wrote `Main.lean`, which ties everything together into the principal result, and at the same time started the analysis of limits in `Limits.lean`. Cassandra then took over `Limits.lean` and finished it. It handles the high-, low- and negative-temperature limits of the distribution.

## `Physlib.lean`

Yuktha set up the dependency on Physlib and wrote the bridge between our definitions and Physlib's canonical ensemble.

## `Independent.lean`, `MaxEntConverse.lean`, `Thermodynamics.lean`

Once we had finished everything we had initially planned, we sat down together (along with Claude; see `AI-USE.md`) to work out which further improvements would make sense for the project, and we outlined together how we would approach each of them. Cassandra had already started a file, `FurtherWork.lean`, on combining independent systems, which became the starting point for `Independent.lean`.

From there, we worked on the new files synchronously. Yuktha mostly did the coding while Cassandra mostly focused on the write-up, but we were working at the same time and talked through each piece together.

## Overall

To finish, we traded laptops, and each of us modified the parts of the project the other had originally written. This let each of us review and edit the other's proofs and write-up, and we then worked together to finalize the edits. Because of this, and because a lot of our work was done side by side on one laptop, the commit history doesn't perfectly reflect who contributed what, but the breakdown above is an accurate summary of how we split the work.