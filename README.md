#  Local Contextual Type Inference (Artifact)

## Overview

This artifact consists of three main parts:

1. Mechanized proofs of the main results in Agda, including soundness, completeness and other properties shown in the paper, excluding the decidability of the algorithmic system, which can be found in `main/proof_agda`.

2. Mechanized proof of the decidability of the algorithmic system in Rocq Prover, which can be found in `main/decidability_rocq`. The reason we use Rocq for this part is simply that Rocq is good at handling numerical automation, which is heavy in the decidability proof.

3. Haskell's prototype implementation of the algorithmic system, including all examples shown in the paper, which can be found in `main/impl_haskell`.

We wish to remark that we briefly mention two variants in the related work section of the paper. Although they are not the main focus of the paper, we provide the mechanization of two variants in the `/variants` folder:

1. `proof_core_top_bot`: a variant extending main system with top and bottom types, which only contains two systems: declarative and intermediate systems, and their soundness and completeness proofs.

2. `proof_variant_right2left`: a variant of main system, which is different from the directionality (left-to-right) of the main system. All properties of the main system are also proved for this variant.

## Kick-the-tires instructions and installation

Reviewers have two options to evaluate the artifact:

1. Directly run the code in their own machine. This is recommended for reviewers who have experience with theorem provers. Our environment setup is not complex but involves three different languages. The artifact is expected to work on recent versions of those languages.

2. Run the code in a virtual machine (QEMU) provided, with the Debian Linux installed. We have installed all dependencies, and put the source code in the root. This is recommended for quick sanity check or kick-the-tires phase if reviewers do not have Agda, Rocq and Haskell installed already.

### Option 1: evaluate the artifact in the host machine

#### 1. Environment setup

Our artifact requires the following dependencies:

1. Agda and its standard library. We tested the code with the version 2.7.0.1 of Agda and the version 2.3 of the standard library. But the latest version of them is expected to work as well.

2. Rocq Prover and CoqHammer tactics. We tested the code with version 8.20.1 of Rocq and version 1.3.2 of CoqHammer. But the latest version of them is expected to work as well.

3. Haskell's GHC and Cabal. We tested the code with version 9.0.2 of GHC and version 3.4.1.0 of Cabal. But the latest version of them is expected to work as well.

The installation of Agda, Rocq and Haskell can be found on their official websites or by package managers like `homebrew` or `apt`.

For Agda standard library, we suggest to follow the instructions in its [GitHub repository](https://github.com/agda/agda-stdlib/blob/master/doc/installation-guide.md).

For CoqHammer tactics, we suggest installing it via `opam`, recommended by its [documentation](https://coqhammer.github.io/#installation). Installing `coq-hammer-tactics` would suffice.

```
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-hammer-tactics
```

#### 2. Running the code

**Main Proof of Agda**

1. Change directory `cd` into `main/proof_agda` folder, and run `make`, which will let Agda check entry file `README.agda` in the proof and generate a `html` folder. This process may take a 2~5 minutes (dependent on the machine), the compilation message of each file will be printed on the terminal.

2. Make sure the compilation finishes without any error, and the `html` folder is successfully generated. Open `html/Implicit.README.html` in a web browser, and you will see a page listing all theorems stated in the paper and their corresponding (clickable) mechanized proofs in Agda.

3. To double-check there is no admitted axioms you can use `grep -r "postulate"` to make sure there's no postulates in the Agda. The printed results should only be from html's configuration files or comments.

**Decidability Proof of Rocq**

1. Change directory `cd` into `main/decidability_rocq/Dec` folder, and run `make` to let Rocq compile. This process may take less than a minute, the compilation message of each file will be printed on the terminal.

2. Make sure the compilation finishes without any error, and the `html` folder is successfully generated. Open `html/toc.html`, you can see a table of contents page, listing language definitions and decidability theorems at the bottom.

3. To double-check there is no admitted axioms you can use `grep -r "Admitted"` and `grep -r "Axiom"` to make sure there's no axioms in the Rocq code. The printed results should only be from html's configuration files or binary files.

**Implementation of Haskell**

1. Change directory `cd` into `main/impl_haskell/Poly` folder, and run `cabal build`. It will download dependencies and build the project. This process may take less one minute.

2. Make sure the compilation finishes without any error.

3. Run `cabal run Poly` will test all examples, and print the results on the terminal.

For codes in the `/variants` folder, the evaluation instructions are similar to the instructions above.

### Option 2: evaluate the artifact in the QEMU virtual machine



## Claims in the paper

We have two claims related to artifacts in the paper:

1. We claim all results shown in the paper, have been formally proven and mechanized in theorem provers. The evaluation instructions can be found in section ([Mechanized Proofs](##Mechanized Proofs)).

2. We claim that we have a prototype implementation, which can run all the examples presented in the paper. The evaluation instructions can be found in section ([Implementation](##Implementation)).

## Mechanized Proofs

For the first claim, it can be verified by checking the mechanized proofs in Agda and Rocq,
by locating the corresponding lemmas and theorems in the code, and compare them with the statements in the paper,
and checking the proofs is proved without any admitted axioms.
To facilitate the reading of the mechanized proofs, we provide a nicely prebuilt HTML, decorated with table of contents on the sidebar.

## Implementation


## Virtual Machine (QEMU)


Make sure the virtual machine is running, and you can use those commands in the host machine:

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