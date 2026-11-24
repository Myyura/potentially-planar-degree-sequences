# Potentially planar degree sequences

[**Recognizing potentially planar degree sequences**](recognizing-potentially-planar-degree-sequences/README.md) by Zhe Zhang and Renwen Tian. The paper directory contains the theorem index, Lean sources, computational checks and third-party licenses.

With [elan](https://github.com/leanprover/elan) installed, build the proofs from the repository root.

```sh
lake exe cache get
lake build
lake env lean recognizing-potentially-planar-degree-sequences/Audit.lean
```

The [disk-fullerene project](disk-fullerene-paper/lean/README.md) has a separate build.
