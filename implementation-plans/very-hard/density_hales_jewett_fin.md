# `DensityHalesJewett.density_hales_jewett_fin`

Source: `DensityHalesJewett/Main.lean`. Blueprint: “Induction on the alphabet.”

## Plan

Induct on `k` starting at `2`; use `dhj_two` for the base and `density_increment` for the successor.
Fix `δ₀ > 0` and obtain a uniform positive increment
`ε := gammaLowerBound k δ₀ / 2`. Choose by Archimedean reasoning a number of stages `R` with
`δ₀ + R*ε > 1`.

Build the required nested dimensions backwards. Let the final target be dimension `1`; at each
earlier stage choose a dimension sufficient for `density_increment` at every density
`ρ ∈ [δ₀,1]`. Since `incrementBound` may depend on `ρ`, define this uniform stage bound by choice
from the uniform-gamma version of the dichotomy, or take a finite maximum over a grid of reachable
lower bounds `δ₀+j*ε`.

Assume a line-free dense family. Repeatedly pull it back to the parameter cube of the selected
subspace. Prove line-freeness is inherited under subspace composition. The line alternative is
therefore impossible, so density rises by at least `ε` at every stage. After `R` steps its density
exceeds one, contradicting `Finset.dens_le_one`.

Package the resulting eventual dimension with the existential witness required by `HasDensityHJ
(k+1)`.

## Risks and verification

The main work is nested-subspace composition and keeping the increment theorem uniform in current
density. Do not rely on arbitrary independent choices in `Parameters.get`. Build the full project.
