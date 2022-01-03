

# How to Run

Install Docker.

Run this

```
docker build . -t haskell:local
```

Put this in your bash profile

```
alias haskell='docker run -it -v $PWD:/home -w /home haskell:local'
```

## Compiling and running

```
haskell ghc --make main.hs
haskell ./main
```

## Interactive coding

```
haskell ghci
```

Load with `:l main`. After edits, reload with `:r`

Run tests by evaluating them like `testParse0`
