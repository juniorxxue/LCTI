#  Local Contextual Type Inference (Artifact)

## Overview

This artifact consists of three main parts:

1. Mechanized proofs of the main results in Agda, including soundness, completeness and other properties shown in the paper, excluding the decidability of the algorithmic system, which can be found in `main/proof_agda`.

2. Mechanized proof of the decidability of the algorithmic system in Rocq Prover, which can be found in `main/decidability_rocq`. The reason we use Rocq for this part is simply that Rocq is good at handling numerical automation.

3. Haskell's implementation of the algorithmic system, including all examples shown in the paper, which can be found in `main/impl_haskell`.

## Kick-the-tires instructions and installation

Reviewers have two options to evaluate the artifact:

1. Directly run the code in their own machine. This is recommended for reviewers who have experience with theorem provers. Our environment setup is not complex and the artifact is tested on recent versions of those languages.

2. Run the code in a virtual machine (QEMU) provided, with the Debian Linux installed. We have installed all dependencies, and put the source code in the root. This is recommended for quick sanity check or kick-the-tires phase if reviewers do not have Agda, Rocq and Haskell installed already.

### Option 1: evaluate the artifact in the host machine


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


Make sure the virtual machine is running, and you can type this command in the host machine:

```
scp -P 5555 -r ./popl26 artifact@localhost:/home/artifact/
```

Here's another helpful command to copy files from the virtual machine to the host machine:

```
scp -P 5555 -r artifact@localhost:/home/artifact/pop26 .
```

## QEMU Instructions

The ICFP 2025 Artifact Evaluation Process is using a Debian QEMU image as a
base for artifacts. The Artifact Evaluation Committee (AEC) will verify that
this image works on their own machines before distributing it to authors.
Authors are encouraged to extend the provided image instead of creating their
own. If it is not practical for authors to use the provided image then please
contact the AEC co-chairs before submission.

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

When preparing your artifact, please also follow the [Submission
Guidelines](https://icfp25.sigplan.org/track/icfp-2025-artifact-evaluation#Submission-Guidelines).