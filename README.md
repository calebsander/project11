# project11
Project 11: Compiler for Jack

## Instructions for running
1. Compile `Main.hs` with the flags `-XFlexibleInstances` and `-XNamedFieldPuns`. (e.g. `stack ghc -- -XFlexibleInstances -XNamedFieldPuns Main.hs -o Main`)
2. Run the executable, passing it the Jack file or directory to be parsed. (e.g. `./Main Square`)
3. It will create a VM file for each parsed Jack file. (e.g. `Square/Main.vm`)

Alternatively, you can just run `./compile.sh` and it will compile the program and run it on all the Jack projects in this directory.