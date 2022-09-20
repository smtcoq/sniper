#!/bin/sh

# Create directory
mkdir paper24
cp coq-paper24.opam Makefile README.md paper24
cd paper24

# Clone Trakt
git clone https://github.com/ecranceMERCE/trakt.git
cd trakt
git checkout tags/1.2+8.13 -b 1.2
cd ..

# Clone SMTCoq
git clone https://github.com/smtcoq/smtcoq.git
cd smtcoq
git checkout with-trakt
echo "-R ../../trakt/theories Trakt" >> src/_CoqProject
cd ..

# Clone Sniper
git clone https://github.com/smtcoq/sniper.git
cd sniper
git checkout preparing-CPP
rm -rf examples archive
mv examples_CPP ../examples
echo "-R ../../trakt/theories Trakt" >> _CoqProject
echo "-R ../../smtcoq/src SMTCoq" >> _CoqProject
echo "-I ../../smtcoq/src" >> _CoqProject
cd ..

# Create zip
cd ..
zip -r paper24.zip paper24



# TODO Anonymize everything!
