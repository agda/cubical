CONTRIBUTING
============

We very much appreciate contributions in the form of pull requests (PRs).
When preparing a PR here are some general guidelines:

- To test your changes before submission, run `make` at the top level,
  which will generate all required `Everything` files in
  `Cubical/README.agda` and then typecheck the latter file.
  If you're using Windows, [here](MAKEWINDOWS.md) are some instructions
  to get the `make` command working.

- Please read through and clean your code before making a PR. Clean
  code has reasonable line length (<100 characters), good indentation,
  appropriate amounts of comments and consistent naming.

- Local definitions should be put in `where`, `let-in` or `private` so
  that it is easy to see which are the main results of a file and
  which are just helper definitions.

- If the code is based on some paper add a reference to the version of
  the paper that the file follows in a comment at the top of the
  file. Avoid calling top-level definitions `thm123`, `lem321`, etc.,
  instead have informative names and put pointers to the theorems and
  lemmas in comments above the definition.

- No global naming scheme for the library was enforced in the past, but new
  contributions should only use names in camel-case. Names of types should
  start with a capital letter and names of terms which are not types should
  start with a lower case letter. However, for names of types that encode a
  property (e.g. `isSet`), we prefer lowercase names. But this is not a
  hard-and-fast rule.

- Use `private variable` to quantify over universe levels at the top
  of the file. All definitions should be maximally universe
  polymorphic.

- Make reasonably many arguments implicit. If you find yourself having
  to provide some argument explicitly most of the time then it should
  not be implicit. The same applies the other way around, if some argument
  most often can be replaced by `_` then it should be made implicit.

- Use `Type ℓ` for universes (so `Set ℓ` is not allowed in order to
  avoid confusion with the type of h-sets).

- All files should start with

  `{-# OPTIONS --safe #-}`

  unless there is a good reason for it not to. The `--cubical` and
  `--no-import-sorts` flags are added in the `cubical.agda-lib` file.

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
  reducing duplicate efforts. If your code contains postulates then it
  should be in a draft PR until the postulates have been filled in.

- We automatically check for whitespace in the end of lines using
  Travis. It is easy to configure emacs so that this is visible while
  editing files by adding `(setq-default show-trailing-whitespace t)`
  to `~/.emacs`. The command `M-x delete-trailing-whitespace` is also
  very useful. It is possible to add a hook that runs this command
  automatically when saving Agda files, by adding the following to your
  `~/.emacs`:
  ```
  ;; delete trailing whitespace before saving in agda-mode
  (defun agda-mode-delete-whitespace-before-save ()
    (when (eq major-mode 'agda2-mode)
      (delete-trailing-whitespace)))

  (add-hook 'before-save-hook #'agda-mode-delete-whitespace-before-save)
  ```

- Use copattern-matching when instantiating records for efficiency.
  This seems especially important when constructing Iso's.

- If typechecking starts becoming slow try to fix the efficiency
  problems directly. We don't want to merge files that are very slow
  to typecheck so they will have to optimized at some point and it's
  often much easier to fix these things directly. If you don't know
  what to try make a draft PR and ask for help.

- It is often useful to give explicit names to the Iso, Equiv and Path
  version of a result. Try to avoid switching between these when
  constructing something, for instance if you want to construct a Path
  out of a series of Iso's then compose the Isos first and then apply
  `isoToPath` once instead of converting all of them to paths and
  composing them as paths.

- Some useful lemmas have specialized versions with higher arity to
  make code easier to read. See for example `isPropΠ2` and `isSetΠ2`
  in [HLevels.agda](https://github.com/agda/cubical/blob/master/Cubical/Foundations/HLevels.agda)
  as well as various versions of function extensionality in
  [FunExtEquiv.agda](https://github.com/agda/cubical/blob/master/Cubical/Functions/FunExtEquiv.agda).

- Unless a file is in the `Core`, `Foundations`, `Codata` or
  `Experiments` package you don't need to add it manually to the
  `Everything` file as it is automatically generated when running
  `make`.

- The `Experiments` folder contains various experiments and nothing in
  the library should depend on something from this folder.
