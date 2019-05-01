# Typedefs

[![Build Status](https://travis-ci.com/typedefs/typedefs.svg?branch=master)](https://travis-ci.com/typedefs/typedefs)

## About

Typedefs is a programming language-agnostic, algebraic data type definition language, written in Idris.

See http://typedefs.com, or play around with examples at [Try Typedefs!](https://try.typedefs.com)

## Build and run

Nix package descriptions, an [Elba manifest](elba.toml) and a [Makefile](Makefile) are provided.

### Nix packages

If you want to build everything, do:

`nix-build`

If you only want to build a specific package:

`nix-build -A typedefs.nix`

### Makefile

Build everything:

```
make build-lib
sudo make install-lib
make build-rest
```

Build a specific package:

`make build pkg=typedefs`

Build documentation:

`make doc-all`

Run tests:

`make test-all`

Install:

`sudo make install-all`

Clean up:

`make clean-all`

### Elba

Build:
```
elba build
```
