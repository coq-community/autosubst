# Autosubst

Autosubst is a Coq library for parallel de Bruijn substitutions

https://www.ps.uni-saarland.de/autosubst



## Requirements

- Coq 8.5
- ssreflect version 1.6 for some examples



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

Please submit bugs reports on https://github.com/tebbi/autosubst/issues



## License

Copyright (c) 2014 Steven Schäfer, Tobias Tebbi

Permission is hereby granted, free of charge, to any person obtaining
a copy of this software and associated documentation files (the
"Software"), to deal in the Software without restriction, including
without limitation the rights to use, copy, modify, merge, publish,
distribute, sublicense, and/or sell copies of the Software, and to
permit persons to whom the Software is furnished to do so, subject to
the following conditions: The above copyright notice and this
permission notice shall be included in all copies or substantial
portions of the Software.  

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.