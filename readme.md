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

## Design
We use one uniform logical clock to represent time elapsed during communication.

### SynchLib
A synchronous network is one where there exists some time bound $\Delta$ such that for any message sent at time *x*, that message is delivered by time *x* + $\Delta$.

#### Safety Properties

With this in mind, we define synchronous networks using the following two safety properties:
1. For all messages, at each time step, either that message has been delivered or less than *x* + $\Delta$ time has passed. *(all messages are delivered on time)*
2. For all messages recieved in the system, that message is a member of the set of sent messages. *(all recieved messages are sent)*

#### Implementation
Synchronous networks do not specify that all messages take the same time to be delivered -- only that all messages will take *no longer* than some time $\Delta$ to be delivered.

So we include random time increments to represent the varying transmission time of messages. Transitions to the time increment state are enabled whenever that increment would not cause a message to expire its delivery bound.

In this way, our library conforms to the formal definition of synchronicity.

## Usage

Because TLA+ is not a standard programming language, NetLib cannot be used via some simple import statement. Instead, one must define a *parallel composition* of their model with NetLib. For an example of this, please view our testing files.

### Required Variables
- Delta: the maximum time bound between network communication. This is treated as a constant.
- t: the logical time. 
- sentMsgs: the set of all messages explicitly sent by our system.
- deliveredMsgs: the set of all messages delivered by our system.
- rcvQueue: queue of all messages to be received. Interactions with rcvQueue are defined by implementers.