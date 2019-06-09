# Contributing

To get started, <a href="https://www.clahub.com/agreements/typedefs/typedefs">sign the Contributor License Agreement</a>.

# Contibuting to Typedefs

There are many reasons why you might want to contribute to Typedefs:

- A feature is missing from Typedefs
- You found a bug and you want to report it
- You want to improve Typedefs

There are many more but we are going to focus on those three in the following document. If you are still lost,
contact one of the maintainers.

## A feature is missing from Typedefs

If there is something you want to achieve but cannot it might just be that Typedefs is missing a crucial feature
that would not only benefit you but many other developers as well. In this case you should:

- Ask for help to see if your goal can be achieved through existing means
- Browse the [issue list](ISSUES) and see if your feature has not been requested already
- Open a new issue if the feature is not already present.

If you want to take the next step check the section "You want to improve Typedefs"

## You found a bug and want to report it

Typedefs isn't perfect. Even though it's written in a dependently typed, it's not immune from human error. And
we still have a battery of test cases to make sure we keep those at a minimum. However some bugs can still surface
and if you find a new one here is what you can do:

- Ask for help to see if you're actually facing a bug and not a behaviour that you did not know about
- Browse the  [issue list](ISSUES) and see if your bug has not been reported
  already
- Open a new issue describing your bug

If you want to take the next step check the section "You want to improve Typedefs"

## You want to improve Typedefs

As we mentionned Typedefs isn't perfect, but it can be improved using your help. If you want to implement a requested
feature or fix a bug that is blocking your workflow, we encourage you to take a look at the project and see if you
can fix it yourself. The steps for this are a bit more involved but should be quite familiar if you've used Idris before.

1. [Fork the project](FORK) and pull it on your computer. (If this is already done you just need to [synchronise with upstream](UPSTREAM).
2. Install the dependencies using `elba` or `nix`. (You can use our [installation tutorial](INSTALLATION) for this step).
3. Pick an issue to work on from [the list of issues](ISSUES).
4. Write the code. It's in Idris! Check out the [Idris webpage](https://www.idris-lang.org/) if you're not familiar with it.
5. Don't forget to run the tests, test your code manually and add a test case.
6. Submit a pull request on the main repository describing what you've done and why.


## A word on the project structure

#### src/CLI/

The directory `CLI/` contains the command line interface to `typedefs-core`. This is what you need to compile in order to get
a new Typedefs binary.

#### src/JS/

The directory `JS/` contains the Javascript API for `typedefs-core`. This is what you need to compile in order to get a new
javascript library for Typedefs.

#### src/Typedefs/

The directory `Typedefs/` contains the idris library that powers Typedefs. The parser, compiler and code generators are all there.
This is the folder you are most likely to be working on if you contribute.
The library is called `typedefs-core`, this is what you will have to import
after installing the library.

[FORK]: https://guides.github.com/activities/forking/
[UPSTREAM]: https://help.github.com/en/github/collaborating-with-issues-and-pull-requests/syncing-a-fork
[ISSUES]: https://github.com/typedefs/typedefs/issues
[INSTALLATION]: ./TUTORIAL_INSTALL.md
