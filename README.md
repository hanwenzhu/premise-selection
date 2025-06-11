# premise-selection

This repository provides a cloud-based Lean premise selector, `Lean.PremiseSelection.Cloud.premiseSelector`.
It sends the current goal state and any new user-defined premises (in current file or imported)
to a cloud server, and returns the top `k` premises recommended by the server.

To use the selector:

```lean
import PremiseSelection

set_premise_selector Lean.PremiseSelection.Cloud.premiseSelector

theorem add_comm_nat (a b : Nat) : a + b = b + a := Nat.add_comm ..

example (a b : Nat) : a + b = b + a := by
  suggest_premises  -- prints premises including `add_comm_nat` and `Nat.add_comm`
```

The premise selector extends the `Lean.PremiseSelection` API introduced in Lean 4 core.

It is developed as part of [LeanHammer](https://github.com/JOSHCLUNE/LeanHammer), which uses the cloud-based premise selector.

## Overview

The premise selection server backend runs a selector model on from Mathlib, Batteries, and Lean core.
It uses an encoder-only transformer to embed premises and the goal state, and retrieves
the top-`k` premises by cosine similarity.

For performance reasons (see below), the number of new premises that can be uploaded
has an upper limit set by the server (e.g. 8192).
A warning will be issued if this limit is surpassed, and extra new premises are truncated.
This truncation prioritizes the new premises in the current module, and then premises in
more recently imported modules.

By default, the cloud premise selector `Lean.PremiseSelection.Cloud.premiseSelector` uses
the backend API hosted by us at `http://leanpremise.net`. To use a custom backend (e.g. in
heavy use cases, machine learning training, or for private premises that you do not wish to
upload to the cloud service), you may set up your own server and then specify a different URL:

```lean
set_option premiseSelection.apiBaseUrl "http://my_api_url"
```

## Run time

The first call to premise selection (by `hammer` or by `suggest_premises`) may be much slower
than subsequent calls, due to caching.
One should expect the first call in any file session (especially in a downstream project of Mathlib,
such as FLT) to be up to 10–20 seconds.
Unrelatedly, the first call in a downstream project after a server restart may also be much slower
(e.g. 2 minutes) due to the time it takes to fill the server-side cache,
but subsequent calls in the downstream repository (by any user) will be much faster.

To optimize for run time, the cloud premise selector has three distinct layers of cache:

* The first layer is on the user side: since the server embedder only takes pretty-printed representations
  of new premises, the user side needs to pretty-print new premises, which is done once per file session,
  and can take up to 10–20 seconds. To make this time reasonably short, there is also an upper bound
  on the number of new premises allowed to be uploaded to the server. Since this is on the user side,
  this extra time is needed for every new file session.
* The second layer is on the server: the server maintains an LRU cache
  of the embeddings of recent new premises uploaded by users.
  (This LRU cache is used only for performance purposes, and is not tied to user identity.)
  Since this is on the server side, the cache serves all users.
* The third layer is during server initialization: the server pre-computes the embeddings of
  all premises in a tagged version of Lean core, batteries, and mathlib.

## Combinators

This repository also provides *premise selector combinators*:

```lean
open Lean PremiseSelection

/-! `orElse` combinator -/

-- Tries the cloud premise selector. If it doesn't work (e.g. network error), use MePo instead.
set_premise_selector
  Cloud.premiseSelector
  <|> mepoSelector (useRarity := true)

/-! `interleave` combinator -/

-- Retrieves `k` premises from the cloud, `k` from MePo, interleaves them by rank,
-- and takes the top-`k` deduplicated premises.
-- This is inspired by Isabelle Sledgehammer's MeSh.
set_premise_selector interleave #[
  Cloud.premiseSelector,
  mepoSelector (useRarity := true) (p := mepoP) (c := mepoC)
]
```

## Testing

To test the selectors:

```lean
lake test
```

This code, as of commit `bdf852`, is tested on Lean versions `v4.18.0` to `v4.20.0-rc5`.

## Links

* Cloud backend:
  * [Server](https://github.com/hanwenzhu/lean-premise-server)
  * [Model training](https://github.com/hanwenzhu/LeanHammer-training)
  * [Data extraction](https://github.com/cmu-l3/ntp-toolkit/tree/hammer)
  * [Model weights](https://huggingface.co/hanwenzhu/all-distilroberta-v1-lr2e-4-bs256-nneg3-ml-ne5) (subject to change)
  * [Extracted dataset](https://huggingface.co/datasets/l3lab/lean-premises)
* LeanHammer:
  * [GitHub repo](https://github.com/JOSHCLUNE/LeanHammer)
