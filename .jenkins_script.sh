#!/bin/bash

set -xe 

cd Examples
stack docker pull
make test
