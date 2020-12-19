# Autosubst

Autosubst is a Coq library for parallel de Bruijn substitutions

https://www.ps.uni-saarland.de/autosubst

## IMPORTANT: Change of Ownership

Ownership of Autosubst was transferred to coq-community. While appropriate redirects where installed during the transfer so that the old remote URLs in existing repository clones still function, Github strongly advises to update local clones to the new remote origin URL. To achieve this, please execute the following in each of your clones of this project:
```
git remote set-url origin https://github.com/coq-community/autosubst.git
```


## Requirements

- Coq 8.10 - 8.12
- to compile `examples/ssr`, ssreflect is needed; version 1.12 will work

## Installation

To install the library on your system, type
```
    make
    sudo make install
```

To build the examples that do not need ssreflect, type
```
    make examples-plain
```

The examples that depend on ssreflect are built with
```
    make examples-ssr
```

To build the documentation (including all examples), type
```
    make doc
```

You can use the file doc/toc.html to browse the documentation.



## Bug Reports

Please submit bugs reports on https://github.com/coq-community/autosubst/issues
