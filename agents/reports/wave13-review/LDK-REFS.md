# Pinned LDK review references

These repositories are read-only external datapoints for the 32-lane wave-13
review. They are **not** vendored into `ln-lean` and are not proof dependencies.

| Repository | Commit | Local path |
|---|---|---|
| `lightningdevkit/ldk-node` | `fa123fed131e27ecc420b77fa7086fcf1ddaebb8` | `/tmp/opencode/ldk-refs/ldk-node` |
| `lightningdevkit/ldk-server` | `c17dc11dde38f88c53457039ddf30c6b90a63ba2` | `/tmp/opencode/ldk-refs/ldk-server` |

Reproduce the pins:

```sh
git -C /tmp/opencode/ldk-refs/ldk-node rev-parse HEAD
git -C /tmp/opencode/ldk-refs/ldk-server rev-parse HEAD
```

Rules for review lanes: read-only inspection; no network; no cargo tests that
fetch; no edits to the pinned clones.
