# Tutorial: Installing Typedefs

This tutorial aims to explain how to install and use _Typedefs_. _Typedefs_ is a language to define _types_ and 
generate type definitions as well as serialisers and deserialisers for a target language. We are going to see later how
to achieve that, right now we are going to focus on how to install the tools.

## 0. Install Idris

Since _Typedefs_ is written using Idris we are going to install the [Idris](IDRIS_HOME) compiler. You can find 
instruction on how to install Idris for your platform here: [https://www.idris-lang.org/download/][IDRIS_DOWNLOAD].


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

Use `:q` to quit.

## 1. Get the source

In order to compile _Typedefs_ you will need to download its source, you can find it on its 
public repo here: [http://github.com/typedefs/typedefs](http://github.com/typedefs/typedefs)

One very easy way to get the code is to clone the project with the following command

```sh
git clone git@github.com:typedefs/typedefs.git
```

## 2. Get elba

For this tutorial we are going to build the project using the [elba package manager][ELBA].
The [README](https://github.com/elba/elba/#elba]) contains the instructions to install elba 
on your system.

The easiest way to install is to use the pre-built binary and add it to your path.

The prebuilt binary can be found on the [release page](https://github.com/elba/elba/releases)



## 3. Compile and install

Once your copy of the repo is downloaded go into its directory (using `cd typedefs` for example) 
and you can now compile the project using 

```sh
elba install
```

This will download all the dependencies and compile the project. The last line printed should be 
something like 

```sh
done! 1 binaries installed into ~/.elba/bin [54.81s]
```

## 4. Try it out

You can try _Typedefs_ by running it with a very simple command:

```sh
~/.elba/bin/typedefs -i "(name bool (+ 1 1))"
```

This assumes that `elba` installed the binary in `~/.elba/bin`. If you have `~/.elba/bin` in your path you can simply 
call

```sh
typedefs -i "(name bool (+ 1 1))"
```

You can now move on to our next tutorial [Using typedefs](./TUTORIAL_USING_TYPEDEFS.md)


[BREW]: https://brew.sh/
[IDRIS_HOME]: https://www.idris-lang.org/
[IDRIS_DOWNLOAD]: https://www.idris-lang.org/download/
[NIX]: https://nixos.org/nix/
[ELBA]: https://github.com/elba/elba/
