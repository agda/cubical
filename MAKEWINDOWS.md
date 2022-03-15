# Instructions for getting `make` to work on Windows

The GNU command `make` does not work out of the box on Windows.
Here are some steps you could take to get `make` working on a Windows machine:

1.  You probably already installed the Chocolatey package manager when
    installing Agda (check by running `choco` in terminal). If not, install it
    from [here](https://chocolatey.org/install).

2.  You need to install the `make` command by running
    ```
    choco install make
    ```

3.  The [makefile](GNUmakefile) runs the `runhaskell` command, which might not
    work on your system. Test this by running in terminal
    ```
    runhaskell
    ```
    If that doesn't work, create a file called `runhaskell.bat` with the contents
    ```
    runghc %*
    ```
    and put this somewhere in your PATH.

4.  Give your user account `Read & Execute` access to `C:\Windows\System32\pthread.dll`

5.  Now, **each time before you run `make`,** run the following command in your terminal:
    ```
    chcp.com 65001
    ```
    so that Haskell can parse UTF-8 characters.
