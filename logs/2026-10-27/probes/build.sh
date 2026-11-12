#!/usr/bin/env bash
# Inside the container (cwd /w): ./build.sh name  -> bin/name from name.lean
name=$1
mkdir -p bin c
nice ionice lean -c c/$name.c $name.lean || exit 1
nice ionice leanc -O3 -o bin/$name c/$name.c || exit 1
