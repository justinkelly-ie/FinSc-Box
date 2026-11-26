# FinSc-Box

**Layer 1 domain-free pure hereditary multiset, `Maxel`, quadratic exchange, and time-horizon freeze-out algebra in total Idris 2.**

```text
FinSc-Box (Layer 1: Pure Box, HereditaryMSet, Maxel, Space n, GohBound, QuadraticTriple)
    │
    ▼
FinSc-Space (Layer 2: Geometry.{Affine, Projective} + Dynamics)
    │
    ▼
FinSc-Lens (Layer 3: External non-perturbing horizons, projective & frame readouts)
    │
    ▼
Finite-Science (Layer 4: Top-of-stack lab & audit suite)
```

## Modules

- [`BoxInt.idr`](src/FinScBox/BoxInt.idr) — Arbitrary-precision signed integer multiplicity scalar (`BoxInt`) with total `O(log N)` binary/Euclidean division (`tdivPosBox`, `rdivPosBox`, `divBox`, `modBox`) bounded by `maxBitScanFuel`.
- [`Interfaces.idr`](src/FinScBox/Interfaces.idr) — Coordinate interfaces (`MonoidCoord`, `GroupCoord`), constructive `SignedCoord` and `Space n`, multiplicity carriers (`SignedBit`, `MultisetBit`), and algebraic interfaces (`MultisetAlgebra`, `MultisetHadamard`, `MultisetOuter`).
- [`Box.idr`](src/FinScBox/Box.idr) — Height-cached zero-pruning AVL container (`Box c k`) and symmetry-compressed 2-parameter `Maxel c a b form` (`GeneralForm`, `SymForm`, `AntisymForm`, `DiagAntisymForm`).
- [`HereditaryMSet.idr`](src/FinScBox/HereditaryMSet.idr) — Recursive `HereditaryMSet c` / `PureMultiset`, `PureMultiset` Goh spread polynumbers (`spreadZHMSet`, `gohPsiMaxelUpTo`), intrinsic `GohBound`/`AnyGohBound`, `Time` horizons, `TimeStream`, Bresenham `paceStreamStep`, and `freezeStateStreamWith`/`freezeTimeStreamWith`.
- [`QuadraticExchange.idr`](src/FinScBox/QuadraticExchange.idr) — Parametric Pythagorean/Gaussian triples (`QuadraticTriple`) and conservative 2-body exchanges (`exchangeQuadraticTriple`, `exchangeQuadratic`).
- [`MultisetCodec.idr`](src/FinScBox/MultisetCodec.idr) — Total canonical base-10/bracket renderer, parser, and `Dec` text recognizer (`recognizePureMultisetText`, `decodeCanonicalMultiset`).
- [`Views.idr`](src/FinScBox/Views.idr) — Non-destructive quantum views (`AntiBoxView`, `DualChannelView`) and streaming peel-work accounting (`streamPeelWorkHMSet`, `fastPeelWorkHMSet`).
- [`BlackRedZoom.idr`](src/FinScBox/BlackRedZoom.idr) — Opposite-polarity scale shifts (`blackShift`, `redShift`) and invertible `zoomTime` / `zoomSpace` transformations.
- [`Lenses.idr`](src/FinScBox/Lenses.idr) — Compile-time `QTT 1` non-perturbing `PureObservation` handle (`0 same : uOut = uIn`) and passive `ExternalLens`.

## Building & Installing

```bash
cd FinSc-Box
idris2 --build FinSc-Box.ipkg
idris2 --install FinSc-Box.ipkg
```

## License

Released under the MIT License.
