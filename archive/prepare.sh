#!/bin/sh

# Create directory
mkdir paper24
cp coq-paper24.opam Makefile README.md paper24.docker paper24
cd paper24

# Clone Trakt
git clone https://github.com/ecranceMERCE/trakt.git
cd trakt
git checkout tags/1.2+8.13 -b 1.2
rm -rf CHANGELOG.md docs example .git .gitattributes .gitignore LICENSE logo.png README.md
cd ..

# Clone SMTCoq
git clone https://github.com/smtcoq/smtcoq.git
cd smtcoq
git checkout with-trakt
echo "-R ../../trakt/theories Trakt" >> src/_CoqProject
rm -rf AUTHORS ci coq-smtcoq.opam dependencies_native.dot doc examples .git .gitignore INSTALL.md LICENSE README.md unit-tests USE.md src/BEST_PRACTICE.md
cd ..

# Clone Sniper
git clone https://github.com/smtcoq/sniper.git
cd sniper
git checkout preparing-CPP
rm -rf examples archive
mv examples_CPP ../examples
echo "-R ../trakt/theories Trakt" >> _CoqProject
echo "-R ../smtcoq/src SMTCoq" >> _CoqProject
echo "-I ../smtcoq/src" >> _CoqProject
rm -rf AUTHORS coq-sniper.opam .git .gitattributes .gitignore LICENSE README.md tests
cd ..

# Remove headers
for i in $(find -name "*.ml*") $(find -name "*.v*") $(find -name "*.elpi")
do
  sed -i ':begin;$!N;N;N;N;N;N;N;N;N;s/(\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*)\n(\*                                                                        \*)\n(\*     SMTCoq                                                             \*)\n(\*     Copyright (C) 2011 - 2022                                          \*)\n(\*                                                                        \*)\n(\*     See file "AUTHORS" for the list of authors                         \*)\n(\*                                                                        \*)\n(\*   This file is distributed under the terms of the CeCILL-C licence     \*)\n(\*                                                                        \*)\n(\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*)//;tbegin;P;D' $i
  sed -i ':begin;$!N;N;N;N;N;N;N;N;N;s/(\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*)\n(\*                                                                        \*)\n(\*     Sniper                                                             \*)\n(\*     Copyright (C) 2021                                                 \*)\n(\*                                                                        \*)\n(\*     See file "AUTHORS" for the list of authors                         \*)\n(\*                                                                        \*)\n(\*   This file is distributed under the terms of the CeCILL-C licence     \*)\n(\*                                                                        \*)\n(\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*)//;tbegin;P;D' $i
  sed -i ':begin;$!N;N;N;N;N;N;N;N;N;s/%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%\n%                           %                     Trakt                       %\n%  _______        _    _    %            Copyright (C) 2022 MERCE             %\n% |__   __|      | |  | |   %     (Mitsubishi Electric R&D Centre Europe)     %\n%    | |_ __ __ _| | _| |_  %        Enzo Crance <enzo\.crance@inria\.fr>       %\n%    | | '\''__\/ _` | |\/ \/ __| %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%\n%    | | | | (_| |   <| |_  % This file is distributed under the terms of the %\n%    |_|_|  \\__,_|_|\\_\\\\__| %   GNU Lesser General Public License Version 3   %\n%                           %  (see LICENSE file for the text of the license) %\n%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%//;tbegin;P;D' $i
  sed -i ':begin;$!N;N;N;N;N;N;N;N;N;s/(\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*)\n(\*                           \*                     Trakt                       \*)\n(\*  _______        _    _    \*            Copyright (C) 2022 MERCE             \*)\n(\* |__   __|      | |  | |   \*     (Mitsubishi Electric R&D Centre Europe)     \*)\n(\*    | |_ __ __ _| | _| |_  \*        Enzo Crance <enzo\.crance@inria\.fr>       \*)\n(\*    | | '\''__\/ _` | |\/ \/ __| \*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*)\n(\*    | | | | (_| |   <| |_  \* This file is distributed under the terms of the \*)\n(\*    |_|_|  \\__,_|_|\\_\\\\__| \*   GNU Lesser General Public License Version 3   \*)\n(\*                           \*  (see LICENSE file for the text of the license) \*)\n(\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*)//;tbegin;P;D' $i
done

# Create zip
cd ..
zip -r paper24.zip paper24
