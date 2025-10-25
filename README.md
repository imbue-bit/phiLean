# phiLean: A Formal Philosophy Library in Lean

![](banner.png)

**phiLean** is an ambitious, open-source project to formalize philosophical arguments, concepts, and problems using the [Lean 4](https://leanprover.github.io/) interactive theorem prover. The core library, `philib`, aims to be for philosophy what `mathlib` is for mathematics: a comprehensive, community-driven repository of formalized knowledge.

> " whereof one cannot speak, thereof one must be silent. "
> — Ludwig Wittgenstein, *Tractatus Logico-Philosophicus*
>
> In `phiLean`, we take this a step further: Whereof one can speak, one should speak precisely. If a philosophical problem cannot be stated in a well-typed, logically consistent form, perhaps the problem lies in the statement itself.

## The Vision

Many philosophical debates are plagued by linguistic ambiguity, hidden assumptions, and flawed reasoning. `phiLean` aims to address this by:

1.  Clarifying, not just answering: Instead of trying to "solve" philosophical problems, `phiLean` provides a framework to dissect them. A poorly formed question often manifests as a *type error* or a logical contradiction under formalization.
2.  Making Axioms Explicit: Philosophical disagreements often stem from unstated foundational beliefs. `phiLean` forces these into the open as explicit `axiom`s, allowing for a clear analysis of how different starting points lead to different conclusions.
3.  Enabling Computational Philosophy: By representing philosophical theories as code, we create a laboratory for exploring their logical consequences, comparing their consistency, and potentially even enabling AI to reason about complex ethical and metaphysical problems.

## Getting Started

### Prerequisites

*   [Lean 4](https://leanprover-community.github.io/get_started.html) installed via `elan`.
*   A C compiler (like `gcc`) for the REPL.

### Installation

1.  Clone the repository:
    ```bash
    git clone https://github.com/imbue-bit/phiLean
    cd phiLean
    ```

2.  Build the project to fetch dependencies (like `mathlib`):
    ```bash
    lake build
    ```

### Using the `phiLean`

The easiest way to interact with `philib` is through our custom REPL. It's a lightweight C wrapper that starts Lean with the `philib` environment pre-loaded.

1.  **Compile the REPL:**
    ```bash
    cd repl
    make
    ```

2.  **Run the REPL from the project root directory:**
    ```bash
    ./repl/philean-repl
    ```

You will be greeted with a `phiLean>` prompt, ready to explore philosophy:

```
$ ./repl/philean-repl
philib environment loaded.
phiLean> #check Philib.Problems.Trolley.UtilitarianAnalysis.pull_lever_is_obligatory
Pilib.Problems.Trolley.UtilitarianAnalysis.pull_lever_is_obligatory : is_obligatory ...

phiLean> open Philib.Ethics.MetaTheories
phiLean> #check realist_excluded_middle
realist_excluded_middle : ∀ (theory : MoralRealism) (judgment : Philib.Ethics.Meta.MoralJudgment), ...
```

## How to Contribute

`phiLean` is a massive undertaking, and we welcome contributions from philosophers, logicians, and programmers alike. Whether you're a Lean expert or a philosophy student new to formal methods, there's a place for you here.

1.  Start Small:
    *   Add more theorems to existing files.
    *   Improve documentation and comments.
    *   Formalize a simple logical paradox in the `Problems` directory.
2.  Tackle a New Concept:
    *   Pick a concept from our planned extensions (e.g., Deontic Logic, Mereology).
    *   Formalize a new philosophical thought experiment.
    *   Implement a different ethical theory (e.g., Virtue Ethics).
3.  Engage with the Community:
    *   Open an issue to discuss a philosophical concept you'd like to formalize.
    *   Review pull requests and provide feedback.

## The Future

Our long-term vision is for `phiLean` to be a standard tool in the philosopher's toolkit. We imagine a future where:
*   Philosophy papers include `philib` code snippets to verify their arguments.
*   AI systems use `philib` to reason about ethical constraints.
*   Students learn logic and philosophy through interactive, formalized examples.
