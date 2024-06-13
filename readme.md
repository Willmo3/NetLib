# NetLib

A TLA+ library for network communication!

## Introduction

As TLA+ model decomposition tools such as CMU SoDA's Recomp-Verify (https://github.com/cmu-soda/recomp-verify) emerge,
TLA+ specifications become increasingly modular.

In addition, modern notions of software robustness emphasize the external environment as a separate entity. *A Behavioral Notion of Software Systems, by Zhang et al* (https://dl.acm.org/doi/abs/10.1145/3368089.3409753) defines software robustness to essentially be the maximum amount of change a software can withstand in its external environment while still functioning.

Therefore, it is now necessary to separate a system's environmental assumptions from its internal implementation.

We present NetLib, a TLA+ library for modeling network communication. We will support three standard models of network communication:
1. Synchronous
2. Asynchronous
3. Partially Synchronous

NetLib encapsulates common network environmental assumptions in a modular and reusable way, enabling modelers to quickly evaluate robustness under varied conditions while avoiding tight coupling between the internal system model and the environmental model.

## Usage

Because TLA+ is not a standard programming language, models cannot simply be imported. Instead, to use NetLib, one must define a *parallel composition* of their model with NetLib. For an example of this, please view our testing files.