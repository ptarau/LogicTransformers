# LogicTransformers

###Transformers from Horn Clause programs to code running  on lightweight Python,  Swift, Julia and C-based VMs 

These are proof-of-concept implementations of several program transformations, see file 

```tnf.pro```,

that generate "assembler" code in directory ``out/``.

A draft paper in  directory ``docs/`` outlines the main ideas about using program transformations to reduce Horn Clause Prolog programs to simple canonical forms for which lightweight implementations are derived.

Make sure you install SWI-Prolog, Python3 as well as (some of) the C, Julia, Swift systems out there, ideally on OS X, but things should run (possibly with minor tweaks) on any Linux as well.

For quick testing type:

```
go <file>
```
where ``progs/<file>.pro`` is one of the files in directory ``progs/``.

The assembler code is placed into a readable *.txt file in directory

``out/`` 

The files are:

```tnf_asm.txt```

corresponding to the *Triplet Normal Form* transformation.
This is  used by all programs except those in
directory ``C/bnf/bnf`` which rely on

```
bnf_asm.txt
```

corresponding to binarization without equational form generation.

After the test passes SWI-Prolog (which generates the assembler file) and then Python, it is ready to be run by Julia, Swift and C, with code variants in their respective directories.

When working with ``Xcode`` for ``C`` and ``Swift``, some edits might be needed as it can only access these files via an absolute path, as its executables land in directories far away. 

``Julia`` code will find these files via a relative path from directory ``julia/``.

