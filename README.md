#  Local Contextual Type Inference (Artifact)

Table of Contents:

1. [Artifact Overview](#artifact-overview): A brief description of the contents of the artifact.
2. [Kick-the-tires instructions and installation](#kick-the-tires-instructions-and-installation): Instructions for setting up the environment and running the code, including an option to run the code in a virtual machine.
3. [Claims in the paper](#claims-in-the-paper): A summary of the claims

## Artifact Overview

This artifact consists of three main parts:

1. Mechanized proofs of the main results in Agda, including soundness, completeness, and other properties shown in the paper, excluding the decidability of the algorithmic system, which can be found in `main/proof_agda`.

2. A mechanized proof of the decidability of the algorithmic system in Rocq Prover, which can be found in `main/decidability_rocq`. We use Rocq for this part because Rocq excels at handling numerical automation, which is heavily used in the decidability proof.

3. A prototype implementation of the algorithmic system in Haskell, including all examples shown in the paper, which can be found in `main/impl_haskell`.

We note that we briefly mention two variants in the related work section of the paper. Although they are not the main focus of the paper, we provide the mechanization of these two variants in the `/variants` folder:

1. `proof_core_top_bot`: a variant extending the main system with top and bottom types, which contains only two systems: declarative and intermediate systems, along with their soundness and completeness proofs.

2. `proof_variant_right2left`: a variant of the main system that differs in directionality (right-to-left instead of left-to-right) from the main system. All properties of the main system are also proven for this variant.

## Kick-the-tires instructions and installation

Reviewers have two options to evaluate the artifact:

1. Run the code directly on their own machine. This is recommended for reviewers who have experience with theorem provers. Our environment setup is straightforward but involves three different languages. The artifact is expected to work with recent versions of these languages.

2. Run the code in a virtual machine (QEMU) with Debian Linux installed. We have installed all dependencies and placed the source code in the root directory. This option is recommended for a quick sanity check or kick-the-tires evaluation if reviewers do not already have Agda, Rocq, and Haskell installed.

### Option 1: Evaluate the artifact on the host machine

#### 1. Environment setup

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

#### 2. Running the code

**Main Agda Proofs**

1. Change directory to the `main/proof_agda` folder and run `make`, which will instruct Agda to check the entry file `README.agda` in the proof and generate an `html` folder. This process may take 2–5 minutes (depending on the machine); the compilation messages for each file will be printed to the terminal.

2. Ensure the compilation finishes without any errors and that the `html` folder is successfully generated. Open `html/Implicit.README.html` in a web browser, and you will see a page listing all theorems stated in the paper along with their corresponding (clickable) mechanized proofs in Agda.

3. To verify there are no admitted axioms, you can use `grep -r "postulate"` to ensure there are no postulates in the Agda code. The results should only come from HTML configuration files or comments.

**Rocq Decidability Proofs**

1. Change directory to the `main/decidability_rocq/Dec` folder and run `make` to compile with Rocq. This process may take less than a minute; the compilation messages for each file will be printed to the terminal.

2. Ensure the compilation finishes without any errors and that the `html` folder is successfully generated. Open `html/toc.html` to see a table of contents page listing language definitions and decidability theorems at the bottom.

3. To verify there are no admitted axioms, you can use `grep -r "Admitted"` and `grep -r "Axiom"` to ensure there are no axioms in the Rocq code. The results should only come from HTML configuration files or binary files.

**Haskell Implementation**

1. Change directory to the `main/impl_haskell/Poly` folder and run `cabal build`. This will download dependencies and build the project. This process may take less than one minute.

2. Ensure the compilation finishes without any errors.

3. Running `cabal run Poly` will test all examples and print the results to the terminal.

For code in the `/variants` folder, the evaluation instructions are similar to those above.

### Option 2: Evaluate the artifact in the QEMU virtual machine

We decided to follow the suggestions from [ICFP 2025 AE](https://icfp25.sigplan.org/track/icfp-2025-artifacts?#VM-Image) to use QEMU as our virtual machine, since we believe that it can work both armed and x86 machines. We provide an image file `disk.qcow` and a startup script `start.sh` (`start.bat` for Windows).

The script is default to assign 4GB of RAM to the virtual machine, which should be sufficient for running our artifact. If you have a machine with more memory and want to allocate more memory to the virtual machine, you can modify the `QEMU_MEM_MB` variable in the `start.sh` script.

The installation of QEMU can be found in the [QEMU Instructions](#qemu-instructions) section at the bottom.

We tested the virtual machine on both Apple chip MacBook and Intel x86 iMac.

**Detailed Instructions**

1. Change directory to the folder containing `start.sh` and `disk.qcow`.

2. Run `./start.sh` to start the virtual machine. This will open a graphical console on the host machine and create a virtualized network interface.

3. In the login page, use the username `artifact` and password `password` to log in.

4. You will see the source code in the `popl26` folder at the home directory. Change directory to this folder.

5. You can do the same steps as in Option 1 to evaluate the artifact.

There are two more helpful commands to facilitate the evaluation in the virtual machine:

1. Since the terminal may not be scrollable in the virtual machine. To read the terminal output, you can redirect the output to a temp file using `>` operator. For example:

```
cabal run Poly > haskell.out
```

2. You can use `scp` command on the host machine to copy output files like `haskell.out` or `html` folder to the host machine. And you can read them on your editors or browsers. For example:

```
scp -P 5555 artifact@localhost:/home/artifact/popl26/main/impl_haskell/Poly/haskell.out .
scp -P 5555 -r artifact@localhost:/home/artifact/popl26/main/proof_agda/html .
```

## Claims in the paper

We make two claims related to the artifact in the paper:

1. We claim that all results shown in the paper have been formally proven and mechanized in theorem provers. The evaluation instructions can be found in the [Mechanized Proofs](#mechanized-proofs) section.

2. We claim that we have a prototype implementation that can run all the examples presented in the paper. The evaluation instructions can be found in the [Implementation](#implementation) section.

## Mechanized Proofs

The first claim can be verified by checking the mechanized proofs in Agda and Rocq,
locating the corresponding lemmas and theorems in the code, comparing them with the statements in the paper,
and verifying that the proofs are completed without any admitted axioms.
To facilitate reading of the mechanized proofs, we provide nicely formatted HTML documentation with a table of contents in the sidebar.

## Implementation


## Virtual Machine (QEMU)


Ensure the virtual machine is running, then you can use these commands on the host machine:

```
scp -P 5555 -r ./popl26 artifact@localhost:/home/artifact/
```

Here's another helpful command to copy files from the virtual machine to the host machine:

```
scp -P 5555 artifact@localhost:/home/artifact/popl26/main/impl_haskell/Poly/outputs/results.out .
scp -P 5555 -r artifact@localhost:/home/artifact/popl26/main/proof_agda/html .
```

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

### Artifact Preparation

Authors should install software dependencies into the VM image as needed,
preferably via the standard Debian package manager. For example, to install
GHC and cabal-install, login to the host and type:

```
$ sudo apt update
$ sudo apt install ghc
$ sudo apt install cabal-install
```

If you really need a GUI then you can install X as follows, but we prefer
console-only artifacts whenever possible.

```
$ sudo apt install xorg
$ sudo apt install xfce4   # or some other window manager
$ startx
```

See Debugging.md for advice on resolving other potential problems.

If your artifact needs lots of memory you may need to increase the value
of the `QEMU_MEM_MB` variable in the `start.sh` script.