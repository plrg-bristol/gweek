# Gweek

A functional logic programming language whose semantics are derived from purely algebraic equations. Gweek supports existential search over first-order data types (naturals, lists, pairs, sums), finitary non-determinism, and unification.

## Try it

An in-browser playground (compiled to WASM) is available at:\
**https://plrg-bristol.github.io/gweek/**

## Building

```
cargo build
```

## Usage

```
gweek [OPTIONS] <source_file>
```

### Search strategies

| Flag | Strategy | Notes |
|------|----------|-------|
| `--bfs` | Breadth-first search | Default. Complete and fair, but memory-heavy. |
| `--dfs` | Depth-first search | Fast and lean, but incomplete on infinite branches. |
| `--iddfs` | Iterative deepening DFS | Complete with low memory; re-explores and deduplicates. |
| `--fair` | Fair round-robin DFS | Complete, no re-exploration. Best general-purpose choice. |

### Other flags

| Flag | Description |
|------|-------------|
| `-o` | Enable peephole optimizer |
| `--timeout <N>` | Timeout in seconds (default: 60) |
| `--first` | Stop after the first solution |
| `--strict` | Strict bind: evaluate RHS before binding (no suspensions) |
| `--eager-vars` | Eagerly resolve variable indirections in the environment |
| `--no-occurs-check` | Skip occurs check in unification (unsound but faster) |

## Example

```
-- Coin change: how many ways to make 20
-- using coins of value 1, 2, or 10?

add :: Nat -> Nat -> Nat
add n m = case m of
    Z -> n
  | S z -> S (add n z).

coin :: Nat
coin = 1 <> 2 <> 10.

change :: Nat -> [Nat]
change n = case n of
    Z -> []
  | S m -> let c = coin in
            exists rest :: Nat.
            add c rest =:= n.
            c : change rest.

change 20.
```

```
$ gweek --fair --first examples/coins.gwk
> [10, 10, 10, 10, 10]
>>> 1 solutions
```

More examples are in the `examples/` directory.

## Language features

- **Types**: `Nat` (with `Z`, `S`, literals), lists (`[a]`), pairs (`(a, b)`), sums (`true`/`false`, `inl`/`inr`)
- **Non-determinism**: `expr1 <> expr2` explores both branches
- **Existential search**: `exists x :: T. body` introduces a logic variable
- **Unification**: `lhs =:= rhs. body` constrains values via unification
- **Pattern matching**: `case expr of Z -> ... | S n -> ...`
- **Recursion**: functions are defined with pattern-matching equations
- **Failure**: `fail` prunes a search branch

## Web playground (local)

```
./serve.sh
```

This builds the WASM target and starts a local server at `http://localhost:8080`. Requires `wasm-pack` and Python 3.
