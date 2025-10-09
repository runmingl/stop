# Artifact Evaluation Instructions

This is the artifact instructions for (conditionally accepted) POPL26 paper *Big-Stop Semantics*. The artifact is a proof script of Agda formalizations of theorems proved in the paper. 

## Download, installation, and sanity-testing

We expect the reviewers to review this artifact in *one* of the following two ways:

### Local development
One can install Agda and its standard library from scratch, following the instructions:
1. Install Agda v2.8.0 ([instructions](https://agda.readthedocs.io/en/v2.8.0/getting-started/installation.html)).
2. Install the standard library v2.3 ([instructions](https://github.com/agda/agda-stdlib/blob/master/doc/installation-guide.md)).

If the reviewer is already an Agda user (e.g. has Agda installed on their local machine), they will very likely have local environment that runs this artifact out-of-box, without any further installation. In particular, this artifact has been tested against the following Agda and standard library versions:

| Agda Version  | Standard Library Version |
|---------------|--------------------------|
| 2.8.0         | 2.3                      |
| 2.7.0.1       | 2.1.1 / 2.2              |
| 2.6.4.3       | 2.0                      |
| 2.6.4.1       | 2.0                      |

To sanity check, locate and unzip `stop.zip`. Inside the `stop` directory, run the following command to load the entire artifact.
```
agda src/Index.agda
```
Alternatively using Emacs or VS Code with Agda emacs mode, open `src/Index.agda` and load the file by via `C-c C-l` (pressing Ctrl-`C` immediately followed by Ctrl-`L`). Depending on the spec of one's local machine, this step should take less than two minutes. 

### Docker development
We provide a docker container (built on an M2 Mac) that contains Agda version 2.8.0 and standard library version 2.3, and our source code in `stop-docker.zip`. 

Run the following commands to start the docker container:
```
docker load < stop-docker.zip 
docker run -it --rm stop:latest
```

Inside the docker container, our source code is in `/opt/stop`. Run the following commands to load the entire artifact.
```
cd /opt/stop
agda src/Index.agda
```

## List of claims

| Section   | Item                                                                     | File                                                                                                 | Name                            | Notes                                                       |
| -------   | ------------------------------------------------------------------------ | -------------------------------------------------------                                              | ------------------------------- | --------------------------------------                      |
| §2.1      | Syntax of call-by-value PCF                                              | [`Language.PCF`](./src/Language/PCF.agda)                                                            | `_⊢_` and `_val`                | Figure 1 and 28                                             |                                       
| §2.2      | Small-step semantics                                                     | [`Language.SmallStep`](./src/Language/SmallStep.agda)                                                | `_↦_↝_` and `_↦*_↝_`            | Figure 2, 3 and 6                                           |      
| §2.3      | Big-step semantics                                                       | [`Language.BigStep`](./src/Language/BigStep.agda)                                                    | `_⇓_↝_`                         | Figure 4 and 7                                              |
| §3, §6.1  | Stack machine semantics                                                  | [`Language.StackMachine`](./src/Language/StackMachine.agda)                                          | `_↦_↝_` and `_↦*_↝_`            | Figure 10 and 11                                            |
| §4, §5    | Big-stop semantics                                                       | [`Language.BigStop`](./src/Language/BigStop.agda)                                                    | `_⇩_↝_`                         | Figure 8                                                    |
| §4.2      | Lemma 13                                                                 | [`Language.Progress`](./src/Language/Progress.agda)                                                  | `progressing-progress`          | Effectful version of lemma 13                               |
| §5        | Lemma 14                                                                 | [`SoundnessCompleteness.SmallStepBigStep`](./src/SoundnessCompleteness/SmallStepBigStep.agda)        | `↦*⇔⇓`                          |                                                             |
| §5.1      | Lemma 15                                                                 | [`SoundnessCompleteness.BigStepBigStop`](./src/SoundnessCompleteness/BigStepBigStop.agda)            | `⇓⇔⇩`                           |                                                             |
| §5.1      | Theorem 16                                                               | [`SoundnessCompleteness.SmallStepBigStop`](./src/SoundnessCompleteness/SmallStepBigStop.agda)        | `↦*⇔⇩`                          |                                                             |
| §5.1      | Corollary 17                                                             | [`Language.BigStop`](./src/Language/BigStop.agda)                                                    | `⇩-trans`                       |                                                             |
| §5.1      | Theorem 18                                                               | [`Language.Progress`](./src/Language/Progress.agda)                                                  | `progress`                      |                                                             |
| §6.2      | Lemma 19                                                                 | [`SoundnessCompleteness.StackMachineBigStop`](./src/SoundnessCompleteness/StackMachineBigStop.agda)  | `↦*→⇩-ε`                        |                                                             |
| §6.2      | Lemma 20                                                                 | [`SoundnessCompleteness.StackMachineBigStop`](./src/SoundnessCompleteness/StackMachineBigStop.agda)  | `↦*→⇩s-ε`                       |                                                             |
| §6.2      | Lemma 21                                                                 | [`SoundnessCompleteness.StackMachineBigStop`](./src/SoundnessCompleteness/StackMachineBigStop.agda)  | `⇩→↦*-ε`                        |                                                             |
| §6.2      | Lemma 22                                                                 | [`SoundnessCompleteness.StackMachineBigStop`](./src/SoundnessCompleteness/StackMachineBigStop.agda)  | `⇩→↦*s-ε`                       |                                                             |

Since submission, the artifact has undergone minor updates. Figures 9 and 12 in the paper will be revised accordingly to reflect the updated lines of code in the artifact. The updated versions of these figures are reproduced below.

| Lemma 14 | Lemma 15 | Theorem 16 | Corollary 17 | Theorem 18 |
|----------|----------|------------|--------------|------------|
| 64       | 28       | 88         | 30           | 18         |

Figure 9: Lines of non-blank, non-comment code of properties of big-stop semantics.

|                     | **Soundness**                                                            |                                                                                | **Completeness**                                                               |                                                                    |
|---------------------|--------------------------------------------------------------------------|--------------------------------------------------------------------------------|--------------------------------------------------------------------------------|--------------------------------------------------------------------|
|                     | Convergent<br>_Lemma 19_                                                 | Divergent<br>_Lemma 20_                                                        | Convergent<br>_Lemma 21_                                                       | Divergent<br>_Lemma 22_                                            |
| **Big-stop**        | 76                                                                       | 72                                                                             | 32                                                                             | 40                                                                 |
|                     | [`↦*→⇩-ε`](./src/SoundnessCompleteness/StackMachineBigStop.agda)         | [`↦*→⇩s-ε`](./src/SoundnessCompleteness/StackMachineBigStop.agda)              | [`⇩→↦*-ε`](./src/SoundnessCompleteness/StackMachineBigStop.agda)               | [`⇩→↦*s-ε`](./src/SoundnessCompleteness/StackMachineBigStop.agda)  |
| **Big-step**        | 81                                                                       | –                                                                              | 29                                                                             | –                                                                  |
|                     | [`↦*→⇓-ε`](./src/SoundnessCompleteness/StackMachineBigStep.agda)         |                                                                                | [`⇓→↦*-ε`](./src/SoundnessCompleteness/StackMachineBigStep.agda)               |                                                                    |
| **Small-step**      | 88                                                                       | 84                                                                             | 68                                                                             | –                                                                  |
|                     | [`↦*→⇒*-ε`](./src/SoundnessCompleteness/StackMachineSmallStep.agda)      | [`↦*→⇒*s-ε`](./src/SoundnessCompleteness/StackMachineSmallStep.agda)           | [`⇒*→↦*-ε`](./src/SoundnessCompleteness/StackMachineSmallStep.agda)             |                                                                    |

Figure 12: Lines of non-blank, non-comment code of soundness and completeness theorems of stack machine.


## Evaluation instructions

The correctness criteria of this artifact is that the Agda code type-checks without errors. This means running `agda src/Index.agda` should complete without any errors.

Reviewers should also be able to interactively view the source code with syntax highlighting in the browser using the HTML functionality of Agda, to check the correspondence between Agda code and on-paper theorems. HTML files can be generated by running:
```sh
agda --html --html-dir=html src/Index.agda
```
The same html files are also available online at [https://www.cs.cmu.edu/~runmingl/stop/](https://www.cs.cmu.edu/~runmingl/stop/).


## Additional artifact description

### Project Structure
The file structure included is as follows:

```
├── AEC.md
├── README.md
├── src
│   ├── Index.agda
│   ├── Prelude.agda
│   ├── Language
│   │   ├── BigStep.agda
│   │   ├── BigStop.agda
│   │   ├── PCF.agda
│   │   ├── Progress.agda
│   │   ├── SmallStep.agda
│   │   ├── StackMachine.agda
│   │   └── Substitution.agda
│   └── SoundnessCompleteness
│       ├── BigStepBigStop.agda
│       ├── SmallStepBigStep.agda
│       ├── SmallStepBigStop.agda
│       ├── StackMachineBigStep.agda
│       ├── StackMachineBigStop.agda
│       └── StackMachineSmallStep.agda
├── stop.agda-lib
```

- [`Index`](./src/Index.agda): Collects all files, for convenience.
- [`Prelude`](./src/Prelude.agda): Contains basic definitions, helper functions, and common utilities used throughout the formalization.
- `Language`
    - [`Language.PCF`](./src/Language/PCF.agda): Contains the typing rules of the PCF language using intrinsic typing (i.e. a term is indexed by a context and a type, where variables are represented by de Bruijn indices into the context).
    - [`Language.BigStep`](./src/Language/BigStep.agda): Contains the standard big step semantics of PCF.
    - [`Language.SmallStep`](./src/Language/SmallStep.agda): Contains the standard structural operational small-step semantics of PCF.
    - [`Language.StackMachine`](./src/Language/StackMachine.agda): Contains the stack machine semantics of PCF.
    - [`Language.BigStop`](./src/Language/BigStop.agda): Contains the Big-Stop Semantics of PCF.
    - [`Language.Progress`](./src/Language/Progress.agda): Contains the progress theorem of PCF using the Big-Stop Semantics.
- `SoundnessCompleteness`: 
    - [`SoundnessCompleteness.SmallStepBigStep`](./src/SoundnessCompleteness/SmallStepBigStep.agda): Proves the soundness and completeness between Small-Step and Big-Step semantics.
    - [`SoundnessCompleteness.StackMachineBigStep`](./src/SoundnessCompleteness/StackMachineBigStep.agda): Proves the soundness and completeness between Stack Machine and Big-Step semantics.
    - [`SoundnessCompleteness.StackMachineSmallStep`](./src/SoundnessCompleteness/StackMachineSmallStep.agda): Proves the soundness and completeness between Stack Machine and Small-Step semantics.
    - [`SoundnessCompleteness.SmallStepBigStop`](./src/SoundnessCompleteness/SmallStepBigStop.agda): Proves the soundness and completeness between Small-Step and Big-Stop semantics.
    - [`SoundnessCompleteness.BigStepBigStop`](./src/SoundnessCompleteness/BigStepBigStop.agda): Proves the soundness and completeness between Big-Step and Big-Stop semantics.
    - [`SoundnessCompleteness.StackMachineBigStop`](./src/SoundnessCompleteness/StackMachineBigStop.agda): Proves the soundness and completeness between Stack Machine and Big-Stop semantics.

### Notations
Throughout the project, we take full advantage of Agda’s excellent support for infix operators to make the code read as naturally as it does on paper. Here are the key notations used:
- `Γ ⊢ τ` is the typing judgment of a term of type `τ` in context `Γ`.
- `v val` is the judgment that `v` is a value.
- `e ⇓ v ↝ a` is the big step evaluation judgment that `e` evaluates to value `v` with effect `a`.
- `e ↦* e' ↝ a` is the small step evaluation judgment that `e` reduces to `e'` with effect `a`.
- `k ▹ e ↦* k' ◃ e' ↝ a` is the stack machine evaluation judgment that the stack machine with stack `k` and code `e` reduces to a new stack `k'` and code `e'` with effect `a`.
- `e ⇩ e' ↝ a` is the Big-Stop evaluation judgment that `e` stops at `e'` with effect `a`.
- `e ↧ e' ↝ a` is the progressing Big-Stop evaluation judgment that `e` is progressing to `e'` with effect `a`.
