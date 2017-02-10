#!/bin/bash

stack ghc -- -XFlexibleInstances -XNamedFieldPuns -Wall Main.hs -o Main || exit

for projectDir in $(ls -d */); do
	./Main $projectDir
done