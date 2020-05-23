CONTRIBUTING
============

We very much appreciate contributions in the form of pull requests (PRs).
When preparing a PR here are some general guidelines:

- Please read through and clean your code before making a PR. Clean
  code has reasonable line length (<100 characters), good indentation,
  appropriate amount of comments and consistent naming.

- Local definitions should be put in `where`, `let-in` or `private` so
  that it is easier to see which are the main results of a file and
  which are just helper definitions.

- If the code is based on some paper add a reference to the version of
  the paper that the file follows in a comment at the top of the
  file. Avoid calling top-level definitions `thm123`, `lem321`, etc.,
  instead have informative names and put pointers to the theorems and
  lemmas in comments above the definition.

- At the moment there is no global naming scheme for the library, so
  just use your best judgment when naming things.

- Use `private variable` to quantify over universe levels at the top
  of the file. All definitions should be maximally universe
  polymorphic.

- Use `Type ℓ` for universes (so `Set ℓ` is not allowed in order to
  avoid confusion with the type of h-sets).

- All files should start with `{-# OPTIONS --cubical --safe #-}`
  unless there is a good reason for it not to.

- It is much easier for us to review and merge smaller and
  self-contained PRs. If a PR changes a lot of files all over the
  library then they will conflict with other PRs making it harder for
  us to merge them. It also takes longer to comment on the code
  if the PR is very big. If you have a large PR please consider
  splitting it into smaller parts that build on each other.

- Large refactoring, renaming, etc., should be done in designated PRs
  that only do one thing.

- Draft PRs are very appreciated so that we can discuss the code as it
  develops. It also helps with knowing who's working on what and
  reducing duplicate efforts.

- We automatically check for whitespace in the end of lines using
  Travis. It is easy to configure emacs so that this is visible while
  editing files by adding `(setq-default show-trailing-whitespace t)`
  to `~/.emacs`.

- Use copattern-matching when instantiating records for efficiency.
  This seems especially important when constructing Iso's.

- It is often useful to give explicit names to the Iso, Equiv and Path
  version of a result. Try to avoid switching between these when
  constructing something, for instance if we want to construct a Path
  out of a series of Iso's then compose the Isos first and then apply
  `isoToPath` once instead of converting all of them to paths and
  composing them as paths.

- Unless a file is in the `Core`, `Foundations`, `Codata` or
  `Experiments` package you don't need to add it manually to the
  `Everything` file as it is automatically generated when running
  `make`.

- The `Experiments` folder contains various experiments and nothing in
  the library should depend on something from this folder.
