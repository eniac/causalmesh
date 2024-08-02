#!/bin/bash -ex

rm -f main
go build -o main internal/base/main.go
bash ./run_stack.sh
