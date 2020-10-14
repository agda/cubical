

This is an attempt to make use of [Booij 2020 - Analysis in Univalent Type Theory](https://abooij.blogspot.com/p/phd-thesis.html) to get a _cauchy-complete archimedean field_ into `--cubical` Agda as [suggested in a Github issue](https://github.com/agda/cubical/issues/286). I am quite verbosely copying from [chapter 4](chapter-4-1.md) of Booij's thesis.

$\int_\Omega f\,\mathrm{d}x$


<!--

Bonus trick: to hide an Agda code block, just put it between html comments

```
{-# OPTIONS --cubical --no-import-sorts --allow-unsolved-metas #-}
-- need --allow-unsolved-metas for generating html
--   see https://github.com/agda/agda/issues/3642
```

-->

The "main" file is 


```
import SyntheticReals
```

extensions of `Cubical.Foundations.Logic` and similar things live in

```
import MoreLogic
```

and developments for "generic" numbers are

```
import Summary
import Number
```

