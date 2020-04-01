# Typedefs-Breakfast

[![Build Status](https://travis-ci.com/typedefs/typedefs.svg?branch=master)](https://travis-ci.com/typedefs/typedefs)

```
                              `     ,            ``     ``.
                               -     -'            ''',"-``.~;`
                                -     ~`            `.'~     `
                                ``    `;`           `.`
                                 .     ',       ,.'      ```
                                  '     ~'      _`,  ```.` ,
                                   '     ~'      ~ ~'.`````
                                    '    `;`     .'.'..`
                                    ``    ';      ,`` `:                   `-',,
                                     '`    _,        ``               `',~~'`
                                      '`    ^`                    `',~,``
                                       '    `^              `;(}]+,`
                                    `   ,    ';         _*\)\+;'
                                    ,::  ;    ;~  `,*((\~.
                                    `` '``'`',:+:^^;,`
                                 ` `:~`,;`-''''`  ``
                                `: ,;_  `   ```    `..
                               ``'-;`;,.       ```````'`
                               ,.',, -'
              `'''''''''''''-'~,;:::~;:,
          .'''             `,'` ,_'`-` ..-`
        `,`               ,`  ,'`,~`'''~  `,
        ,'                `', '-,' -~'_' `',
        ' `-.....`        `',' -~: `,:'..  '
        ``       `...........'.'.'.`      '
         '                               '
          '`                            '
           ``                         .'
             .`                    `--
               ``````````````````-``
```

## About

Typedefs-breakfast is a programming language allowing to define recipes for delicious breakfast
leveraging the power of an f-algebra describing types! Each term in this algebra will define
delicious cerealisation functions in your target language. Cereals wouldn't be complete without
milk so each ceralisation function comes with a functionality to `pourMilk` in order to interpret
the cereals back into hydration.

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

There is a complete tutorial on how to compile and install typedefs using the elba
package manager [here](docs/TUTORIAL_INSTALL.md).

In most cases it should be just as easy as:

```
elba install
```
