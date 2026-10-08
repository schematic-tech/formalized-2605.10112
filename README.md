# The Dominating 4-Colour Theorem

A complete Lean 4 formalization of the paper *The Dominating 4-Colour Theorem* by António Girão, Freddie Illingworth, Bojan Mohar, Sergey Norin, Raphael Steiner, Youri Tamitegama, Jane Tan, David R. Wood, and Jung Hon Yip ([arXiv:2605.10112](https://arxiv.org/abs/2605.10112)). The formalization was generated autonomously by [Schematic](https://github.com/schematic-tech)'s Lean proof engine Hydra.

The results from the article are formalized in `DominatingFourColour/`, including the theorems:
```lean
/-- The Dominating 4-Colour Theorem. -/
theorem dominating_four_colour
    {V : Type u} [Fintype V]
    (G : SimpleGraph V) :
    HasNoDominatingKModel G 5 → G.Colorable 4 :=
  …

/-- Every graph of chromatic number at least five has a dominating K5 model. -/
theorem five_chromatic_has_dominating_K5_model
    {V : Type u} [Fintype V]
    (G : SimpleGraph V) :
    FiveChromaticOrMore G → HasDominatingKModel G 5 :=
  …
```

## Dependencies

- [`FourColorTheorem`](https://github.com/schematic-tech/formalized-fct): the Four Color Theorem---also formalized by Schematic Hydra.
- [`Schematic.Math`](https://github.com/schematic-tech/math): reusable graph theory, including planar embeddings and graph minors---from Schematic's formal math library.

## Build

```sh
lake update
lake build
```

`lake build` checks certificates by kernel reduction. For faster routine builds:

```sh
lake -R -K nativeDecide=true build
```

## License

Apache-2.0. See `LICENSES/Apache-2.0.txt`.
