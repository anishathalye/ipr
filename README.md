# IPR [![Build Status](https://github.com/anishathalye/ipr/workflows/CI/badge.svg)](https://github.com/anishathalye/ipr/actions?query=workflow%3ACI)

Theory of information-preserving refinement (IPR) formally verified in Coq.

<p align="center">
    <img src="https://raw.githubusercontent.com/anishathalye/assets/master/ipr/ipr-definition.png" width="500" alt="The definition of information-preserving refinement">
</p>

IPR relates two state machines with differing interfaces and captures the notion that the implementation implements the specification but leaks no additional information through its behavior. [Knox (OSDI'22)](https://pdos.csail.mit.edu/papers/knox:osdi22.pdf) applies IPR to verify hardware security modules, ensuring that the cycle-precise wire-I/O-level behavior of the implementation leaks no more information than a functional specification.

## Organization

This repository contains a Coq formalization of the theory of information-preserving refinement (IPR), including a proof of its transitivity, as well as several proof techniques for IPR.

- `Common.v`, `Tactics.v`: basic definitions and tactics
- `Machine.v`: state machines, traces, equivalence, and simulation-based proofs
- `Driver.v`: driver language and semantics
- `Emulator.v`: emulator language and semantics
- `Definition.v`: real world, ideal world, and IPR definition
- `Utils.v`: utility functions
- `ProofStrategy/`: proof strategies for IPR
    - `Transitivity.v`: transitivity of IPR
    - `Equivalence.v`: equivalence proof strategy, where state machine equivalence implies IPR-equivalence
    - `Lockstep.v`: lockstep proof strategy, applicable when there is a one-to-one correspondence between spec and implementation steps
    - `Simulation.v`: functional-physical simulation proof strategy, a generalization of forward simulation, applicable when there's a simulation relation that holds in between spec-level operations
    - `Commute.v`, `Compose.v`, `Wrap.v`, `Self.v`: lemmas used in the above proofs

## Dependencies

The code in this repository only depends on the [Coq proof assistant](https://coq.inria.fr/).

## Building

You can run `make` to check the proofs.

## Citation

Knox (OSDI'22) introduces the definition of information-preserving refinement:

```bibtex
@inproceedings{knox:osdi22,
    author =    {Anish Athalye and M. Frans Kaashoek and Nickolai Zeldovich},
    title =     {Verifying Hardware Security Modules with Information-Preserving Refinement},
    month =     {jul},
    year =      {2022},
    booktitle = {Proceedings of the 16th USENIX Symposium on Operating Systems Design and Implementation~(OSDI)},
    address =   {Carlsbad, CA},
}
```

This formalization was developed as part of a follow-up paper that is under submission. This formalization is also a part of Anish's PhD thesis. To get a copy of these pre-publication documents, email Anish at [aathalye@mit.edu](mailto:aathalye@mit.edu).
