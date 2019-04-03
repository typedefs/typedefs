# Typedefs

Programming language agnostic type construction language based on polynomials.

[![Build Status](https://travis-ci.com/typedefs/typedefs.svg?branch=master)](https://travis-ci.com/typedefs/typedefs)

## About

See http://typedefs.com.

## Building

Nix package descriptions and a Makefile is provided with build instructions.

### Nix packages

Build everything:

`nix-build`

Build a specific package:

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
