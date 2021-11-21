# Instructions for getting `make` to work on Windows

The GNU command `make` does not work on Windows out of the box. Here are the steps I took to get it to work on my Windows 10 machine:

1.  You probably already installed the Chocolatey package manager when installing Agda (check by running `choco` in terminal). If not, install it from [here](https://chocolatey.org/install).

2.  You need to install the `make` command by running
    ```
    choco install make
    ```

3.  The makefile runs the `runhaskell` command, which might not work on your system. Test this by running in terminal
    ```
    runhaskell
    ```
    If that doesn't work, you'll have to change line 5 of `~/GNUmakefile` to
    ```
    RUNHASKELL?=runghc
    ```

4.  Give your user account `Read & Execute` access to `C:\Windows\System32\pthread.dll`

5.  In terminal, run
    ```
    chcp.com 65001
    ```
    so that Haskell can parse UTF-8 characters.