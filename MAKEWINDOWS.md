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

3.  Give your user account `Read & Execute` access to `C:\Windows\System32\pthread.dll`

4.  Now, **each time before you run `make`,** run the following command in your terminal:
    ```
    chcp.com 65001
    ```
    so that Haskell can parse UTF-8 characters.
