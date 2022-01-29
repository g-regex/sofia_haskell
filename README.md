## Dependencies
This software was developed using the following libraries:

* ghc-8.10.4
* yesod-1.6.1.1
* yesod-persistent-1.6.0.7
* sqlite-3.35.5

The web interface was tested on:

* firefox-91.5.0
* google-chrome-97.0.4692.99

The documentation was generated using:

* haddock-2.24.0
* pdfTeX, Version 3.141592653-2.6-1.40.22
* minted 2017/07/19 v2.5
* pygments-2.10.0

Compatibility with other versions of these libraries has not been tested.

## Usage
The proof assistant is used via a web browser interface. Before you can run it,
you have to rename the `theory_examples.db3` to `theory.db3` or download a
theory database from an online version of Sofia and place it in the source
directory. In either case you have to ensure that a valid `theory.db3` is
present in the source directory.

To run Sofia locally, compile the source code with
```shell
$ ghc --make WebInterface.hs
```
and then start it with:
```shell
$ ./WebInterface.hs
```
Alternatively you can also run it with:
```shell
$ runhaskell WebInterface.hs
```

Then point your web browser to `http://localhost:3000`. Further help can be found within the web interface by typing `:help`.
