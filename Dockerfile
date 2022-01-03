FROM haskell:latest
RUN cabal update && cabal install --lib unordered-containers
