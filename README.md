# Introduction to Software Verification (2360342) — Exercises

In-class exercises for the course at the Technion. Each exercise is in its own folder.

| # | Exercise | Lecture | Open |
|---|----------|---------|------|
| 1 | [Explicit-state CTL model checking](01-explicit-ctl-mc/) | 3–4 | [![Open in Colab](https://colab.research.google.com/assets/colab-badge.svg)](https://colab.research.google.com/github/TechnionFV/intro-fv-exercises/blob/main/01-explicit-ctl-mc/ctl_mc_class.ipynb) |

## How to run

**GitHub Codespaces** (recommended)

[![Open in GitHub Codespaces](https://github.com/codespaces/badge.svg)](https://codespaces.new/TechnionFV/intro-fv-exercises?quickstart=1)

1. Click the button above (or **Code → Codespaces → Create codespace on main**).
2. Wait for the setup to finish; it installs everything in `requirements.txt`.
3. Open the exercise notebook, e.g. `01-explicit-ctl-mc/ctl_mc_class.ipynb`.
4. If asked for a kernel, choose **Python 3.12**.

**Google Colab**

Click the *Open in Colab* button of the exercise, then **File → Save a copy in Drive** so you can keep your work.
The first cell of the notebook installs what it needs.

**Your own machine**

```bash
pip install -r requirements.txt
jupyter notebook
```

## Exercise 1 — Explicit-state CTL model checking

A complete explicit-state CTL model checker: the formula as a graph of its sub-formulas,
a post-order traversal, and one procedure per operator. You implement **EU** and **EG** and
check them on the microwave example from the lecture; then we add **fairness**.

* `ctl_mc_class.ipynb` — the notebook
* `ctlmc.py` — given helpers (models, parser, drawing, SCCs)
