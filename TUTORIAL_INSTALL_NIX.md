# Tutorial: Using Typedefs

This tutorial aims to explain how to install and use _Typedefs_. _Typedefs_ is a language to
define _types_ and generate type definitions as well as serializers and deserializers for a target
language. We are going to see later how to achieve that, right now we are going to focus on how to
install the tool.

## 1. Install using Idris

For this tutorial we are going to build and install typedefs manually using its source code ans the
idris compiler.

In order to compile idris code you will need the [Idris](IDRIS_HOME) compiler. You can find instruction on how to install idris for your platform here: [https://www.idris-lang.org/download/][IDRIS_DOWNLOAD].


#### Shortcut: Mac OS

If you're using Mac OS, you can use [`brew`][BREW] to install Idris by typing this on your terminal

```sh
brew install idris
```

#### Check it's working

Once Idris is installed you can check it works by typing

```sh
idris
```

And you should get

```sh
     ____    __     _
    /  _/___/ /____(_)____
    / // __  / ___/ / ___/     Version 1.3.2-git:ed4d4cf30
  _/ // /_/ / /  / (__  )      http://www.idris-lang.org/
 /___/\__,_/_/  /_/____/       Type :? for help

Idris is free software with ABSOLUTELY NO WARRANTY.
For details type :warranty.
Idris>
```

## 2. Get the source

In order to compile _typedefs_ you will need to download it's source, you can find it on its public repo here: [http://github.com/typedefs/typedefs](http://github.com/typedefs/typedefs)

One very easy way to get the code is to clone the project with the following command

```sh
git clone git@github.com:typedefs/typedefs.git
```

## 3. Get nix

For this tutorial we are going to build the project using the [nix package manager](NIX). The main page ([https://nixos.org/nix/](https://nixos.org/nix/)) contains the instruction to install nix on your system.

## 4. Compile and install

Once your copy of the repo is downloaded go into its directory (using `cd typedefs` for example) and you can now compile the project using

```sh
nix-build -A typedefs-parser
```

This will download all the dependencies and compile the `typedefs-parser` project.

[BREW]: https://brew.sh/
[IDRIS_HOME]: https://www.idris-lang.org/
[IDRIS_DOWNLOAD]: https://www.idris-lang.org/download/
[NIX]: https://nixos.org/nix/
