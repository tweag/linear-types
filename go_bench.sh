#! /usr/bin/env bash

stack build
stack exec -- bench-cursor $* 

