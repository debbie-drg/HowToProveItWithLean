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
* Open the folder for the repository in the terminal and run `lake build`. Keep in mind that this will compile `mathlib4`, so it will take a while. It is preferred that `lake build` is run on a terminal with VSCode conflicts. Otherwise, VSCode may be using some of the files that lake wants to use and it will error out.
