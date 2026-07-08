(lang dune 3.21)

(using rocq 0.11)

(name rocq-sniper)

(generate_opam_files)

(source
 (github smtcoq/sniper))

(license CECILL-C)

(authors
 "Valentin Blot"
 "Louise Dubois de Prisque"
 "Chantal Keller"
 "Pierre Vial")

(maintainers
 "Chantal Keller <ckeller@lmf.cnrs.fr>"
 "Vincent Lafeychine <vincent.lafeychine@proton.me>")

(package
 (name rocq-sniper)
 (synopsis "A Rocq plugin for general proof automation")
 (description
  "Sniper is a Coq plugin that provides a new Coq tactic, snipe, for general proof automation.\n\nThis plugin is an extension of SMTCoq, a plugin to safely call external SMT solvers from Coq. Sniper extends SMTCoq by translating (a subset) of Coq goals into first-order logic before calling SMTCoq.\n\nThe translation is implemented through a combination of modular, small transformations that independently eliminate specific aspects of Coq logic towards first-order logic. These small transformations are safe, either generating proof terms on the fly (certifying transformations) or being proved once and for all in Coq (certified transformations).\n")
 (tags
  ("category:Computer Science/Decision Procedures and Certified Algorithms/Decision procedures"
   "category:Miscellaneous/Coq Extensions"
   "keyword: SMT"
   "keyword: automation"
   "logpath:Sniper"))
 (depends num rocq-smtcoq))
