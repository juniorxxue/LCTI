#  Local Contextual Type Inference (Artifact)

## Artifact Overview

This artifact consists of three main parts:

1. Mechanized proofs of the main results in Agda. This includes the formalization of three systems: the declarative system (Contextual System F, a variant of Implicit System F), the intermediate system (matching subtyping), and the algorithmic system. It also includes the proofs of soundness and completeness between these systems. All stated theorems excluding the decidability of the algorithmic system are proved in Agda.

2. A mechanized proof of the decidability of the algorithmic system in Rocq Prover. We use Rocq for this part because Rocq excels at handling numerical automation, which is heavily used in the decidability proof.

3. A prototype implementation of the algorithmic system in Haskell, which can type-check all the examples presented in the paper.

We note that we briefly mention two variants in the related work section of the paper. Although they are not the main focus of the paper, we provide the mechanization of these two variants in the `/variants` folder:

1. `proof_core_top_bot`: a variant extending the main system with top and bottom types, which contains only two systems: the declarative and intermediate systems, along with their soundness and completeness proofs.

2. `proof_variant_right2left`: a variant of the main system that differs in directionality (right-to-left instead of left-to-right) from the main system. All properties of the main system are also proven for this variant.

## Kick-the-Tires Instructions

Reviewers have two options to evaluate the artifact:

1. Run the code directly on their own machine. This is recommended for reviewers who have experience with theorem provers. Our environment setup is straightforward but involves three different languages. The artifact is expected to work with recent versions of these languages.

2. Run the code in a virtual machine (QEMU) with Debian Linux installed. We have installed all dependencies and placed the source code in the root directory. This option is recommended for a quick sanity check or kick-the-tires evaluation if reviewers do not already have Agda, Rocq, and Haskell installed.

After setting up the environment or downloading the virtual machine image, we expect that it will take less than 30 minutes to walk through the whole process.

### Option 1: Evaluate the Artifact on the Host Machine

#### 1. Environment Setup

Our artifact requires the following dependencies:

1. Agda and its standard library. We tested the code with Agda version 2.7.0.1 and standard library version 2.3. However, the latest versions are expected to work as well.

2. Rocq Prover and CoqHammer tactics. We tested the code with Rocq version 8.20.1 and CoqHammer version 1.3.2. However, the latest versions are expected to work as well.

3. Haskell GHC and Cabal. We tested the code with GHC version 9.0.2 and Cabal version 3.4.1.0. However, the latest versions are expected to work as well.

Installation instructions for Agda, Rocq, and Haskell can be found on their official websites or through package managers such as `homebrew` or `apt`.

For the Agda standard library, we recommend following the instructions in its [GitHub repository](https://github.com/agda/agda-stdlib/blob/master/doc/installation-guide.md).

For CoqHammer tactics, we recommend installing them via `opam`, as recommended by the [documentation](https://coqhammer.github.io/#installation). Installing `coq-hammer-tactics` will suffice.

```
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-hammer-tactics
```

#### 2. Running the Code

**Main Agda Proofs**

1. Change to the `main/proof_agda` directory and run `make`, which will instruct Agda to check the entry file `README.agda` in the proof and generate an `html` folder. This process may take 2–5 minutes (depending on the machine); compilation messages for each file will be printed to the terminal.

2. Ensure that the compilation finishes without any errors and that the `html` folder is successfully generated. Open `html/Implicit.README.html` in a web browser, and you will see a page listing all theorems stated in the paper along with their corresponding (clickable) mechanized proofs in Agda.

3. To verify there are no admitted axioms, you can use `grep -r "postulate"` to ensure there are no postulates in the Agda code. The results should only come from HTML configuration files or comments.

**Rocq Decidability Proofs**

1. Change to the `main/decidability_rocq/Dec` directory and run `make` to compile with Rocq. This process may take less than a minute; compilation messages for each file will be printed to the terminal.

2. Ensure that the compilation finishes without any errors and that the `html` folder is successfully generated. Open `html/toc.html` to see a table of contents page listing language definitions and decidability theorems at the bottom.

3. To verify there are no admitted axioms, you can use `grep -r "Admitted"` and `grep -r "Axiom"` to ensure there are no axioms in the Rocq code. The results should only come from HTML configuration files or binary files.

**Haskell Implementation**

1. Change to the `main/impl_haskell/Poly` directory and run `cabal build`. This will download dependencies and build the project. This process may take less than one minute.

2. Ensure that the compilation finishes without any errors.

3. Running `cabal run Poly` will test all examples and print the results to the terminal.

For code in the `/variants` folder, the evaluation instructions are similar to those above.

### Option 2: Evaluate the Artifact in the QEMU Virtual Machine

We decided to follow the suggestions from [ICFP 2025 AE](https://icfp25.sigplan.org/track/icfp-2025-artifacts?#VM-Image) to use QEMU as our virtual machine, as we believe it can work on both ARM and x86 machines. We provide an image file `disk.qcow` and a startup script `start.sh` (`start.bat` for Windows).

The script defaults to assigning 4GB of RAM to the virtual machine, which should be sufficient for running our artifact. If you have a machine with more memory and want to allocate more memory to the virtual machine, you can modify the `QEMU_MEM_MB` variable in the `start.sh` script.

The installation of QEMU can be found in the [QEMU Instructions](#qemu-instructions) section at the bottom.

We tested the virtual machine on both Apple silicon MacBook and Intel x86 iMac.

**Detailed Instructions**

1. Change to the directory containing `start.sh` and `disk.qcow`.

2. Run `./start.sh` to start the virtual machine. This will open a graphical console on the host machine and create a virtualized network interface.

3. On the login page, use the username `artifact` and password `password` to log in.

4. You will see the source code in the `popl26` folder in the home directory. Change to this directory.

5. You can follow the same steps as in [Option 1: 2. Running the code](#2-running-the-code) to evaluate the artifact.

There are three additional helpful commands to facilitate the evaluation in the virtual machine:

1. Since the terminal may not be scrollable in the virtual machine, to read the terminal output, you can redirect the output to a temporary file using the `>` operator. For example:

```
cabal run Poly > haskell.out
```

2. You can use the `scp` command on the host machine to copy output files like `haskell.out` or the `html` folder to the host machine. You can then read them in your editors or browsers. For example:

```
scp -P 5555 artifact@localhost:/home/artifact/popl26/main/impl_haskell/Poly/haskell.out .
scp -P 5555 -r artifact@localhost:/home/artifact/popl26/main/proof_agda/html .
```

3. You can also replace the source code in the virtual machine with the source code on the host machine. First remove the existing `popl26` folder in the virtual machine, then use the `scp` command on the host machine to copy the `popl26` folder from the host machine to the virtual machine. For example:

```
scp -P 5555 -r ./popl26 artifact@localhost:/home/artifact/
```

## Claims in the Paper

We make two claims related to the artifact in the paper:

1. We claim that all results shown in the paper have been formally proven and mechanized in theorem provers.

2. We claim that we have a prototype implementation that can run all the examples presented in the paper.

## Full Evaluation

### Mechanization

The entry point to read Agda code is the `README.agda` file in the `main/proof_agda/Implicit/` folder, which lists all theorems stated in the paper along with their corresponding mechanized proofs in Agda. They are structured as follows:

```agda
-- Theorem 3.1 (Reflexivity of Subtyping)
import Implicit.Decl.Typing using (s-refl-∞)

-- Theorem 3.2 (Transitivity of subtyping)
import Implicit.Decl.Trans using (s-trans')

-- Theorem 3.3 (Soundness to Implicit System F)
import Implicit.Annotatability.Soundness using (sound)
```

We recommend reading the Agda code in `html` format, where you can click on the imported theorems to navigate to their definitions and proofs.
Another way to read the Agda code is through the well-maintained folder structure:

1. `Language`: language definitions, including syntax of types, terms, environments, and auxiliary judgments appearing in the rules.

2. `Decl`: declarative system, including typing rules and subtyping rules, along with their properties, corresponding to the system presented in Section 3 in the paper.

3. `Interm`: intermediate language, including matching subtyping, corresponding to the system presented in Section 4 in the paper.

4. `Algo`: algorithmic system, including typing rules and subtyping rules, along with their properties, corresponding to the system presented in Section 5 in the paper.

5. `Algo2Interm` and `Interm2Algo`: soundness and completeness proofs between the algorithmic system and the intermediate system.

6. `Decl2Interm` and `Interm2Decl`: soundness and completeness proofs between the declarative system and the intermediate system.

7. `Annotatability`: the formalization of Implicit System F, including the soundness and completeness (also called annotatability) proofs between Contextual System F and Implicit System F, corresponding to the system presented in Section 3.3 in the paper.

For the Rocq code, the file structure is straightforward, and the decidability theorems can be found in `Dec.v`.

**Discrepancies Between the Paper and the Mechanization**

We would like to point out a few discrepancies between the paper and the mechanization. All of these are due to the trade-off between ease of presentation and ease of mechanization, and we believe that they do not affect the correctness of the mechanization.

1. **Binding Techniques:** The mechanization uses a well-scoped de Bruijn representation for the syntax, including with several shifts over language constructs, while the paper uses named variables for better readability.

2. **Environmental Representation:** In the paper, the three systems use three different kinds of environments, while in the mechanization, we use a single unified environment representation for all three systems to simplify the implementation, while enforcing some well-formedness invariants.

3. **Invariants:** In the paper, we omit most invariants enforced for the system while explaining them in the text, such as `regular`. In the mechanization, we inline those invariants into the base case of the rules.

4. **Encoding All Functions as Relations:** In the paper, we present some operations as functions, including `grounding` and environmental lookup. In the mechanization, we encode almost all of them as relations to facilitate reasoning about them, since functions would block case analysis in Agda, and relations are more suitable for dependent pattern matching.

5. **Unifying Rules:** In the paper, for simplicity of presentation, we unify some rules, while in the mechanization they are split into multiple rules. These include the following:

   - Instantiability (Figure 3): In the paper, we present a single rule for the $\forall L$ rule, while in the mechanization we split it into two: `s-∀l` and `s-∀l-no-appear` in `Decl/Subtyping.agda`. The side conditions in the two rules are the same as those in the paper.

   - `DS-Arr` rule (Figure 3): In the paper, we present a single rule for function subtyping with meta-operations on the counters. In the mechanization, we specialize it into three rules, `s-arr₁`, `s-arr₂`, and `s-arr₃`, corresponding to the three cases of the meta-operation. Note that in `s-arr₃` we omit a premise since it is a tautology for declarative subtyping.

   - `IS-Var-L` rule (Figure 4): In the paper, we present a single left rule for matching variables (with arbitrary counters), while in the mechanization we split the counters (along with their supertypes) to three cases, corresponding to three rules: `s-svar-l`, `s-svar-𝕚`, `s-svar-𝕔` and `s-svar-𝕥`. We do a similar simplification for the algorithmic system.

For the remaining aspects, we believe they are straightforward translations from the paper to the mechanization, and we strive to match the Agda notation to the notation in the paper.

### Implementation

In the file `main/impl_haskell/Poly/README.md`, we provide a detailed explanation of how to run this code, the meaning of the output, and a table listing all the examples presented in the paper.

## Reusability Guidelines

To our knowledge, we are the first to mechanize local type inference algorithms, which are widely used in practical programming languages such as Java, Scala, and TypeScript. We believe that not only our conceptual model of contextual type inference, but also our mechanization techniques can lay a solid foundation for future mechanization of practical type inference algorithms.

Specifically, we request to be badged as Reusable based on the following reasons:

1. Our infrastructure of well-scoped de Bruijn can be reused for mechanizing other type systems, especially polymorphic type systems. We found that by tracking the number of free variables in the environment, we can avoid many pitfalls when reasoning. Well-scoped de Bruijn is not a new idea, but it is rarely used in mechanizing complex type inference algorithms. We believe that our mechanization can serve as a good reference for future mechanization of polymorphic type systems.

2. Our mechanization is suitable for adding extensions for new language constructs and features. Our mechanizations of the three systems are separated into different folders, with their metatheory unentangled. The metatheory for the declarative system is very simple, allowing for the study of new features (including new typing and subtyping rules) without worrying about other algorithmic details.

3. Our Haskell implementation can be tested with more inputs. This is documented in the `README.md` file in the `main/impl_haskell/Poly` folder.


## QEMU Instructions

QEMU is a hosted virtual machine monitor that can emulate a host processor
via dynamic binary translation. On common host platforms QEMU can also use
a host provided virtualization layer, which is faster than dynamic binary
translation.

QEMU homepage: https://www.qemu.org/

### Installation

#### OSX
``brew install qemu``

#### Debian and Ubuntu Linux
``apt-get install qemu-kvm``

On x86 laptops and server machines you may need to enable the
"Intel Virtualization Technology" setting in your BIOS, as some manufacturers
leave this disabled by default. See Debugging.md for details.


#### Arch Linux

``pacman -Sy qemu``

See the [Arch wiki](https://wiki.archlinux.org/title/QEMU) for more info.

See Debugging.md if you have problems logging into the artifact via SSH.


#### Windows 10

Download and install QEMU via the links at

https://www.qemu.org/download/#windows.

Ensure that `qemu-system-x86_64.exe` is in your path.

Start Bar -> Search -> "Windows Features"
          -> enable "Hyper-V" and "Windows Hypervisor Platform".

Restart your computer.

#### Windows 8

See Debugging.md for Windows 8 install instructions.

### Startup

The base artifact provides a `start.sh` script to start the VM on unix-like
systems and `start.bat` for Windows. Running this script will open a graphical
console on the host machine, and create a virtualized network interface.
On Linux you may need to run with `sudo` to start the VM. If the VM does not
start then check `Debugging.md`

Once the VM has started you can login to the guest system from the host.
Whenever you are asked for a password, the answer is `password`. The default
username is `artifact`.

```
$ ssh -p 5555 artifact@localhost
```

You can also copy files to and from the host using scp.

```
$ scp -P 5555 artifact@localhost:somefile .
```

### Shutdown

To shutdown the guest system cleanly, login to it via ssh and use

```
$ sudo shutdown now
```

See Debugging.md for advice on resolving other potential problems.