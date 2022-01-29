## Dependencies
This software was developed using the following libraries (compatibility with other versions has not been tested):

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

## Usage
The proof assistant is used via a web browser interface. To run it locally, compile the source code with
```shell
$ ghc --make WebInterface.hs
```
and then start it with:
```shell
$ ./WebInterface.hs
```

Then point your web browser to `http://localhost:3000`. Further help can be found within the web interface by typing `:help`.
