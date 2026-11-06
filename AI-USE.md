# Week of 10/18 - 10/24:

## Defs.lean/Variational.lean/Limits.lean/Gibbs.lean:
AI was utilized here in order to give us some ideas of what definitions would be necessary since we haven't gone over probability distribution logic in class. Once that was done, we did the proof by hand in Defs.lean. However, we did need AI assistence in order to determine some of the logic for handling exponents as we haven't discussed this. AI did not fully supply proofs - it just gave us hints towards functions to use cause we couldn't really get answers from the apply? and exact? due to the vast number of steps in between. One example of a hint was in the proof of sum_boltzmann where AI told us to this exactly "-- Hint: `Finset.sum_div`, then `div_self`."

Also I used AI to write comments on what defs were provided because I wanted nicer formatting than I had initially. For each file, it read through what we had and wrote comments to tag what the main findings were (the docstring like tag at the top of the file is what was ai generated + the comments about what each lemma/theorem is was cleaned up with ai from some messy math to cleaner!)


## Main.lean
When creating Main.lean, I noticed that the proof was really difficult to make so I asked Claude for advice on how to simplify this. It recommended making an extra two lemmas to handle the exxtra work (entropy_eq_neg_sum, freeEnergy_boltzmann). So I went ahead and added those two in and then the proof became a little simpler to do!
