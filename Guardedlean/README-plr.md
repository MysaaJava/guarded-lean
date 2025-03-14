Here is a summary to the work i did during my 5 month internship in München with Kenji Maillard

## Studying the ToT structure
I first studied the ToT structure made by Møgelberg & Bahr.
They were using a smaller structure than the categorical one (the restrict map was only defined from n to n+1, and not for any m < n)
My first work was to prove that this simplified version equivalent to the categorical one. This is `TTooTTequivalence` defined in file `ToposOfTrees.lean`.
In the same time, I changed the previous work of Møgelberg & Bahr to use Mathlib's CategoryTheory. I added categorial structure gradually, this work can be found in the following files:
- `ToT/Basic.lean` contains the structure type ToT and the categorical structure associated
- `ToT/CartesianClosed.lean` show that this category is cartesian closed (minimal logic)
- `ToT/Later.lean` the later modality and the associated fixpoint theorem

## Hyperdoctrine
Then, i wanted to write _categorically_ that we could use first order logic on objects of ToT. For that, the adequate structure was _Hyperdoctrines_. They were not present in Mathlib, therefore i wrote them myself in `Logic.lean`.

Last step was to add hyperdoctrine structure to the topos of trees, and this was done in file `ToT/FirstOrder.lean`.

By the same time, i added more concepts around hyperdoctrins, like Hyperdoctrines functors. I compiled them into a bifunctor _Hyp_ defined in file `CatHyp.lean`.

## Modal hyperdoctrines
I constructed the bicatgory _Lex_ of categories with finite limits and limit-preserving functors in file `CategoryTheory/Lex.lean`

The goal is now to describe everything using a modal hyperdoctrine, this is work in progress in the file `ToT/Modal.lean` and `DependentRightAdjoint.lean`.


## Other files
- `Lemmas.lean` Useful lemmas
- `Categories.lean` Categorical lemmas/structures
- `CategoryTheory/PreservesChosen.lean` a notion of limit-preserving functors with computational content to build the limit
- `CategoryTheory/Bicategory/Opposite.lean` a notion of opposite bicategory, where the 1-cells and the 2-cells are inverted (Mathlib's Opposite only does it for 1-cells)
- `ToTType.lean` a file where i tried to recreate the objects of Møgelberg & Bahr from the one i defined myself.
- `Syntax.lean` is the syntax part of Møgelberg & Bahr, extracted
- `Basic.lean` is from Møgelberg & Bahr, i don't know what's inside