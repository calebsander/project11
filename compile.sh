#!/bin/bash

stack ghc -- -XFlexibleInstances -XNamedFieldPuns -Wall Main.hs -o Main || exit

for projectDir in Average ComplexArrays ConvertToBin Pong Seven Square; do
	./Main $projectDir
done