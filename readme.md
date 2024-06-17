
# NetLib

A TLA+ library for network communication!

## Introduction

As TLA+ model decomposition tools such as CMU SoDA's Recomp-Verify (https://github.com/cmu-soda/recomp-verify) emerge, TLA+ specifications become increasingly modular.

In addition, modern software robustness separates systems from their external environments, such as networks and user interactions.

For instance, *A Behavioral Notion of Software Systems, by Zhang et al* (https://dl.acm.org/doi/abs/10.1145/3368089.3409753) defines robustness as the maximum amount of change a software system can withstand in its environment while still functioning.

With this decoupling of system and environment comes a need for modular environmental modeling libraries.

We present NetLib, a TLA+ library for modeling network communication. We will support three standard network models:

1. Synchronous
2. Asynchronous
3. Partially Synchronous

NetLib encapsulates common network environmental assumptions in a modular way, enabling modelers to quickly evaluate robustness under varied conditions while evading tight coupling between system and environmental models.

## Design
We use one uniform logical clock to represent time elapsed during communication.

For simplicity, our network is represented by a single sending agent and single receiving agent.

### Properties:

#### Recieved Messages Sent:
In all our networks, messages that are received should have been sent by some recognized client.

#### Messages Recieved in Time

##### In the Synchronous Context:
A synchronous network is one where there exists some time bound $\Delta$ such that for any message sent at time *x*, that message is delivered by time *x* + $\Delta$.

So, for all messages, at each time step, either that message has been delivered or less than *x* + $\Delta$ time has passed. *(all messages are delivered on time)*

##### In the Asynchronous Context:
By definition, no time bound can be placed on asynchronous message delivery time.

##### In the Partially Synchronous Context:
In a partially synchronous network, there exists some time *GST* such that the network behaves synchronously for all messages sent after *GST*.

### Implementation
We include random time increments to represent the varying transmission time of messages. Transitions to the time increment state are enabled whenever that increment would not cause a message to expire its delivery bound.

## Usage

Because TLA+ is not a standard programming language, NetLib cannot be used via some simple import statement. Instead, one must define a *parallel composition* of their model with NetLib. For examples of this, please view our testing files.

We define a network in two models:
1. NetLib, representing the actual network channel
2. NetClient, representing the clients

And compose these two models together.

To implement our library, write your own client and composition!
