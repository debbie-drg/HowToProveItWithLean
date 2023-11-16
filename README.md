# Solutions and explanations to How to prove it with Lean

This repository contains my explanations and exercise solutions for the online book [*How To Prove It with Lean*](https://djvelleman.github.io/HTPIwL/) by Daniel J. Velleman.

In order to run these files:

* [Install Lean 4](https://github.com/leanprover/lean4/blob/master/doc/quickstart.md).
  Alternatively, if you do not wish to use VSCode, you can manually install `elan`, the Lean version manager. On Linux/Mac, run
  
  ```bash
  curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
  ```

  On Windows, run
  
  ```powershell
  curl -O --location https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1
  powershell -ExecutionPolicy Bypass -f elan-init.ps1
  del elan-init.ps1
  ```

* Clone the repository
* Open the folder for the repository in the terminal and run

```bash
lake exe cache get
lake build
```

This will download a precompiled version of [mathlib4](https://github.com/leanprover-community/mathlib4).

Some resources to browse Mathlib:
* The [mathlib4 documentation](https://leanprover-community.github.io/mathlib4_docs/index.html)
* [Loogle](https://loogle.lean-lang.org/), a pattern matching search engine for Mathlib4.
* [Moogle](https://www.moogle.ai), semantic search over Mathlib4. 

Some resources to learn Lean
* [Natural Numbers Game](https://adam.math.hhu.de/#/g/hhu-adam/NNG4), a game introducing the basics of Lean by proving properties of the Natural Numbers, similar to `NaturalNumbers.lean`
* Velleman's [How to prove it with Lean](https://djvelleman.github.io/HTPIwL/), which accompanies the book [How to prove it](https://users.metu.edu.tr/serge/courses/111-2011/textbook-math111.pdf).
* [Mathematics in Lean](https://github.com/leanprover-community/mathematics_in_lean), the de facto standard interactive textbook about doing mathematics in Lean.
* [Lamperg's introduction](https://github.com/JLimperg/regensburg-itp-school-2023) from the  2023 International Summer School on Interactions of Proof Assistants and Mathematics in Regensburg.
* [Lean Zulip](https://leanprover.zulipchat.com/), an online forum/chat about Lean.
