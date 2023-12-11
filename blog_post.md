## Abstract
In this project, we implemented an interpreter for the btor2 hardware description language. As there does not currently exist an interpreter for btor2, we felt that creating one would add to the overall language ecosystem. In addition, we implemented an optimization to the memory format and benchmarked it against our initial naive interpreter. We indeed observed that the optimization boosted performance on all benchmarks we surveyed.

## What is btor2?
btor2 is a model checking language designed for hardware; it provides this functionality at a word level, and also includes functionality for persistent state. Words of arbitrary length can be represented as bit vectors, and states that are present in the hardware (for instance, in registers or in local memory) can be represented as arrays. btor2 is an extension of btor, which is a similar model checking language for hardware which only supports bit vectors and one-dimensional bit vector arrays (in contrast, btor2 can have multidimensional arrays). btor2 as a language is useful for verifying generated low-level hardware code.

## Motivation

The creators of btor2 included three key tools: a parser, a random state simulator, and a witness checker, all written in C. Notably missing from this list is an interpreter for the language; though the random state simulator does exist, it does not test any of the many bit vector operations that btor2 supports, choosing to focus on arrays instead. In addition, though the witness checker does check whether a given state is a valid execution state for a given program, it does not do so in a constructive way—no actual interpretation is performed. We also feel that an interpreter for btor2 would be useful, since it would allow users to run arbitrary btor2 programs to ensure their correctness. Thus, we elected to write an interpreter for btor2 as this project.

The current codebase is primarily written in C and C++, which although performant, are not very type-safe and not the most intuitive to reason about when writing programming language utilities. We therefore chose to write our interpreter in Rust, as it provides similar performance to C and C++ while also being much safer and resulting in more modern code.

## Design

We first sketched out a basic design of the structure of our project. We found a library called btor2tools-sys that provides Rust bindings for the btor2 parser that the creators released, so we chose to use that for our parser. As far as the end-to-end structure goes, we first read in a btor2 file from the command line, parse it using the Rust bindings, and then run our interpreter on the resulting parse. 

The structure of btor2 instructions is relatively simple; it’s similar to bril in that there are no nested instructions, and it’s even simpler in that there is no control flow: all instructions are executed in one pass from top to bottom. Thus, the parser for btor2 returns an iterator containing representations of each line of the original btor2 program. Our interpreter then will simulate running each instruction from top to bottom, saving the results of each instruction in its state and outputting the relevant results at the end.

## Implementation

We first wrote a representation of bit vectors in Rust. It turns out that Rust already has a builtin BitVec crate, but as the bit vectors in btor2 require more functionality than the standard Rust crate, we wrote a wrapper BitVector module that provided all the necessary functionality. We wrote a helper method in each module that corresponds to every btor2 instruction, along with a few helper methods for initializing bit vectors with various means. The bitwise operations were largely relegated to the Rust BitVec implementation, and for the arithmetic operations, we converted our bit vectors to Rust big integers and performed operations in that manner.

Next, we wrote a naive interpreter. It iterates through all the instructions, executes each instruction naively, and stores the result in our environment data structure. We chose to use a vector to represent the environment with the indices being the line numbers and the values being the bit vectors. Nothing was specifically done for optimization purposes on this first pass; we wanted to first ensure correctness.

We then wrote a more optimized version of our interpreter, aiming to improve the memory locality. Instead of allocating new memory for every bit vector and storing them in a vector, we instead computed how much memory each program would need by making a pass through and noting the number of bits in each sort for each line of input. Then, we represented our environment as one large array of bits, which would represent the data, along with a list of offsets that represented where the result of each line of computation was stored. In order for this to work, we had to modify our interface for our interpreter: now, instead of performing operations on BitVector objects, it would now dispatch all operations to the environment, which would perform them directly on the bit array in memory. While this did cause us to have to write two separate versions of the interpreter, it should not be difficult to refactor our original interface to work better with the new one.

We chose not to implement the overflow opcodes, as we felt as though they were not very interesting to do and would not be very applicable in our tests.

## Difficulties

The primary difficulty we dealt with while working on this project was ensuring that the libraries we were using were correct and up-to-date. Because this language is not yet very widely used, the tools that currently exist for it have not been extensively tested. As such, we ran into two main issues while writing the interpreter. Firstly, the Rust bindings for the parser were not up to date with the latest version of Rust (which we contributed a fix for). Secondly, the C parser supplied by the creators of btor2 discarded the immediates for instructions (in particular, the indices that were used for slicing, sign-extending, and zero-extending bitvectors) were lost. We think this issue was never noticed because the random simulator ignored these immediates. We ended up having to modify the C parser code directly to fix this bug, and we’ll contribute a PR in that repo shortly.

## Evaluation

We wrote two main types of end-to-end tests to ensure correctness for this assignment: many small core tests that tested each major opcode we supported for combinational logic (we did not manage to complete the stateful logic in time), along with a large stress test generator used for performance testing purposes. In order to observe non-trivial results with the small core test, we repeatedly simulated them for a varying number of iterations. The key motivation is that the ultimate goal for this btor2 interpreter is to serve as a drop-in replacement for simulating the primitives for the Calyx interpreter—Cider. In its current state, Calyx standard library uses Verilog (a hardware design language) to represent primitives. To simulate these primitives, we currently reimplement them in Cider. However, this introduces a tight coupling. An improvement would be to compile the SystemVerilog designs into BTOR using Yosys, an open synthesis suite, which would then be simulated using our interpreter. This way, we envision a majority of the use cases involving a large chain of small btor2 primitives as opposed to a single large file. Thus by simulating on small core tests for a varying number of iterations we are able to more accurately assess the performance and effectiveness of our interpreter in real-world scenarios. 

Next, we used these tests to benchmark the performance of our original interpreter versus our optimized interpreter. We show our results in the below tables; we chose to average together the results over all core benchmarks and report the results for our larger stress test separately.

Below are the results for our core benchmarks. We ran three runs for each core benchmark for a given number of iterations and averaged the runtimes over all runs over all core benchmarks.

| Number of Iterations  | 10             | 100            | 1000            | 10000            | 100000             | 1000000              |
|-------------------|----------------|----------------|-----------------|------------------|--------------------|----------------------|
| Naive interpreter | 2.0 ± 3.7 ms | 3.0 ± 3.1 ms | 11.4 ± 5.1 ms | 86.0 ± 26.0 ms | 814.3 ± 241.3 ms | 7778.9 ± 1506.2 ms |
| Faster intepreter | 1.9 ± 3.3 ms | 1.9 ± 1.3 ms | 6.0 ± 2.9 ms  | 42.6 ± 16.4 ms | 397.8 ± 117.7 ms | 3705.3 ± 930.0 ms  |

Below are the results for our stress test. We again ran three runs for the stress test for a given number of iterations and again averaged the runtimes over all runs.

| Number of Trials  | 10           | 100           | 1000          | 10000           | 100000             | 1000000             |
|-------------------|--------------|---------------|---------------|-----------------|--------------------|---------------------|
| Naive interpreter | 2.2 ± 1.9 ms | 11.6 ± 2.9 ms | 92.8 ± 6.1 ms | 904.4 ± 33.8 ms | 10752.8 ± 180.1 ms | 53675.5 ± 326.8 ms  |
| Faster intepreter | 2.1 ± 1.2 ms | 3.7 ± 0.9 ms  | 42.1 ± 4.0 ms | 388.7 ± 18.0 ms | 4073.9 ± 280.2 ms  | 27950.3 ± 1032.5 ms |

From the above tables, we can see that for large numbers of iterations, the faster interpreter has a signifcant speedup over the naive interpreter, sometimes by well over 2x. Thus, we can conclude that our optimization of storing the memory as a bit slice and avoiding unnecessary memory allocations was indeed successful.

## Conclusions

Overall, we successfully implemented an interpreter for the btor2 language, along with an optimization to the interpreter that improves performance. We greatly enjoyed working on this project, as it allowed us to gain more familiarity with Rust along with getting a glimpse into how language tools are used in the real world for research purposes. Lastly, it was rewarding for us to see the optimizations to the interpreter we implemented play out in real time when benchmarking both versions.
