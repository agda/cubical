Installation of agda/cubical
============================

The cubical library should compile on the latest official release
of Agda:

https://github.com/agda/agda

This file contains detailed instruction for how to install this on
Linux and Mac. Windows users might be able to use Cygwin to mimic
these instructions, but this hasn't been tested.

There are three main ways of installing the development version of Agda:

1. Using cabal `v2-build`: https://www.haskell.org/cabal/
2. Using cabal sandboxes: https://www.haskell.org/cabal/
3. Using stack: https://docs.haskellstack.org/

We recommend whichever approach that works for you. This INSTALL file
contains some detailed instructions for installing Agda using either
cabal and stack. For more instructions and general documentation of
Agda see:

https://agda.readthedocs.io/

cabal v2-install instructions
=============================

cabal `v2-build` is a new operating mode, which makes projects
not interfere with each other. To download and compile the development
version Agda with a `v2-build`, you need to download recent (2.4 or later)
version of [`cabal-install`](https://www.haskell.org/cabal/download.html).
Then, execute following:

```
> cabal v2-update
> git clone https://github.com/agda/agda
> cd agda
> touch doc/user-manual.pdf
> cabal v2-install agda agda-mode
```

This should put the agda and agda-mode executables in the folder
`~/.cabal/bin` (the location can be configured with `--symlink-bindir` flag).

In order to be able to access these on your system you need to add
them to your `$PATH` environment variable. On a typical Linux/Mac
installation this can be done by adding

```
export PATH=$HOME/.cabal/bin:$PATH
```

in your `~/.bashrc` or `~/.bash_profile`. Here `path/to/agda` is the
absolute path to where you cloned the agda repository. In order for
this change to take effect you then have to run

```
> source ~/.bashrc
```

or

```
> source ~/.bash_profile
```

or restart the terminal. You should now be able to run:

```
> agda --version
```

to see that agda has been properly installed and is available in your
`$PATH`. You then also want to setup the agda-mode for emacs:

```
> agda-mode setup
```

Once this works go to a suitable directory and run

```
> git clone https://github.com/agda/cubical
> cd cubical
```

You can additionally run `make` to typecheck all of the agda/cubical files, otherwise they will be checked as needed. To test that it
works in emacs run

```
> emacs Cubical/Core/Primitives.agda
```

and then type `C-c C-l`. This should now load the file and you can
start developing your own cubical files.

You can also register cubical as a library to depend on it in your own
Agda developments:

https://agda.readthedocs.io/en/latest/tools/package-system.html


cabal sandbox install instructions
==================================

In order to have you Agda installation not interfere with any other
Haskell packages that you might have installed it is recommended to
use a sandbox (that installs agda locally in a folder and not globally
on your system). To download and compile the development version Agda
in a cabal sandbox do the following:

```
> git clone https://github.com/agda/agda
> cd agda
> cabal sandbox init
> cabal update
> make
```

If you have cabal v2 installed the sandbox command should be replaced
by `cabal v1-sandbox init`.

If the above commands succeed this the agda and agda-mode executables
will be in the folder `agda/.cabal-sandbox/bin`. In order to be able
to access these on your system you need to add them to your `$PATH`
environment variable. On a typical Linux/Mac installation (using Bash
or Zsh as the shell) this can be done by adding

```
export PATH=/path/to/agda/.cabal-sandbox/bin:$PATH
```

in your `~/.bashrc` or `~/.bash_profile`. Here `path/to/agda` is the
absolute path to where you cloned the agda repository. In order for
this change to take effect you then have to run

```
> source ~/.bashrc
```

or

```
> source ~/.bash_profile
```

or restart the terminal. You should now be able to run:

```
> agda --version
```

to see that agda has been properly installed and is available in your
`$PATH`. You then also want to setup the agda-mode for emacs:

```
> agda-mode setup
```

Once this works go to a suitable directory and run

```
> git clone https://github.com/agda/cubical
> cd cubical
```

You can additionally run `make` to typecheck all of the agda/cubical files, otherwise they will be checked as needed. To test that it
works in emacs run

```
> emacs Cubical/Core/Primitives.agda
```

and then type `C-c C-l`. This should now load the file and you can
start developing your own cubical files.

You can also register cubical as a library to depend on it in your own
Agda developments:

https://agda.readthedocs.io/en/latest/tools/package-system.html


stack install instructions
==========================

In order to install Agda using stack do the following:

```
> git clone https://github.com/agda/agda
> cd agda
> stack build --stack-yaml stack-"version".yaml
```

Where "version" is a suitable version of ghc (for example 8.6.3). This
should put the agda and agda-mode executables in the folder
`agda/.stack-work/install/.../.../.../bin`.

where `...` are system and setup dependent. In order to be able to
access these on your system you need to add them to your `$PATH`
environment variable. On a typical Linux/Mac installation this can be
done by adding

```
export PATH=/path/to/agda/.stack-work/install/.../.../.../bin:$PATH
```

in your `~/.bashrc` or `~/.bash_profile`. Here `path/to/agda` is the
absolute path to where you cloned the agda repository. In order for
this change to take effect you then have to run

```
> source ~/.bashrc
```

or

```
> source ~/.bash_profile
```

or restart the terminal.

You can also run

```
> stack install
```

which will copy `agda` and `agda-mode` to your `~/.local/bin` folder.
Once these executables are in your PATH you should be able to run:

```
> agda --version
```

to see that agda has been properly installed and is available in your
`$PATH`. You then also want to setup the agda-mode for emacs:

```
> agda-mode setup
```

Once this works go to a suitable directory and run

```
> git clone https://github.com/agda/cubical
> cd cubical
```

You can additionally run `make` to typecheck all of the agda/cubical files, otherwise they will be checked as needed. To test that it
works in emacs run

```
> emacs Cubical/Core/Primitives.agda
```

and then type `C-c C-l`. This should now load the file and you can
start developing your own cubical files.

Registering the cubical library
===============================

You can also register cubical as a library to depend on it in your own
Agda developments:

https://agda.readthedocs.io/en/latest/tools/package-system.html

On a Linux/Mac installation you need the following files (where
`/path/to/cubical.agda-lib` has been replaced by the path to the
`cubical.agda-lib` file):

```
$ cat .agda/defaults
cubical
$ cat .agda/libraries
/path/to/cubical.agda-lib
```
