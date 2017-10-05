#!/usr/bin/env bash
DOCKER_REPO=tweag/linear-types
DOCKER_VERSION=popl18
DOCKER_TAG=$DOCKER_REPO:$DOCKER_VERSION

docker build -t $DOCKER_TAG .
# docker push will fail if you don't have access to the Tweag I/O organisation on Dockerhub
docker push $DOCKER_TAG
