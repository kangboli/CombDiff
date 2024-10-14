# The scoping of NEIN


A nein expression captures global variables and local variables and a symbolic copy.
It then constructs a function that takes the symbolic copies as the input.
The generated code is then applied to the values in the global and local variables.

- The local variables will shadow the globals.

# JIT once

If you put a macro inside a julia function, it gets expanded and compiled every time.
This can be a significant overhead.

NEIN can express functions, so you have the option of writing the whole function in
NEIN. The function will then be compiled only once.

