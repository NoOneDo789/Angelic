[How to install]

mkdir fresh_dir
cd fresh_dir

opam switch create freshopam 4.10.0 &&
eval $(opam env --switch=freshopam) &&
opam pin add coq 8.13.2 -y &&
opam repo add coq-released https://coq.inria.fr/opam/released &&
opam config env &&
opam pin add coq-paco 4.1.1 -y && opam pin add menhir 20230608 -y && opam pin add coq-ordinal 0.5.0 -y

(move artifact to fresh_dir and unzip)

cd Angelic
./configure x86_64-linux
make -j -k

[Important Files]

- [common/Simulation.v]: Definition of Semantics and Simulation
- [common/Behaviors2.v]: Definition of Behavior
- [common/Adequacy.v]: Statement and Prove of Adequacy Lemma
- [backend/Unusedglobproof.v]: Correctness proof of Unusedglob
- [backend/Renumberproof.v]: Correctness proof of Renumber
