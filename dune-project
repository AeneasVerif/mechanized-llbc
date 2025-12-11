(lang dune 3.16)
(using coq 0.9)

(generate_opam_files true)

(package
 (name mechanized-llbc)
 (authors "Alban Reynaud Michez" "Vincent Rébiscoul")
 (maintainers "Alban Reynaud Michez" "Vincent Rébiscoul")
 (synopsis "Formalization of the LLBC model for the Rust programming language")
 (depends
   (coq (>= 9.0))
   (coq-stdpp (>= 1.11)))
)
