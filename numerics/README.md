# Numerical checks

These scripts check supporting identities for I1, I2 and I3.
They print results and exit with an error if a check fails. They do not write files.

With Python 3.11 or later, create a local environment and install the dependencies
from the repository root:

```sh
python3 -m venv .venv
.venv/bin/python -m pip install -r numerics/requirements.txt
```

`venv` keeps dependencies in this folder. Run any script directly, for example:

```sh
.venv/bin/python numerics/I1/moments.py
```

| Script | Checks |
| --- | --- |
| [I1/moments.py](I1/moments.py) | Gaussian moments, leverage and carry corrections |
| [I1/dynamic_identification.py](I1/dynamic_identification.py) | Dynamic excitation, lag identification and Gaussian scores |
| [I2/hedging_identities.py](I2/hedging_identities.py) | Gaussian hedge weights, grids and tail budgets |
| [I2/smoothing_rates.py](I2/smoothing_rates.py) | Smoothing exponent identities and Gaussian integrals |
| [I2/date_allocation.py](I2/date_allocation.py) | Weighted date budgets and quantile grids |
| [I3/four_put.py](I3/four_put.py) | Shifted-put moments and a rational information-gain certificate |
| [I3/capital_frontiers.py](I3/capital_frontiers.py) | Obstacle, projection and finite-capital identities |
| [I3/uniform_moments.py](I3/uniform_moments.py) | Uniform-marginal payoff moments and risk derivatives |
| [I3/index_comparison.py](I3/index_comparison.py) | Index-projection bounds and exact advantage margins |
