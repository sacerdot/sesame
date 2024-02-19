(lang dune 3.13)

(name sesame)

(generate_opam_files true)

(source
 (github sacerdot/sesame))

(authors "Claudio Sacerdoti Coen")

(maintainers "Claudio Sacerdoti Coen")

(license MIT)

(documentation https://url/to/documentation)

(package
 (name sesame)
 (synopsis "Code for the paper \"IMELL Cut Elimination with Linear Overhead\"")
 (description "This library implements the Strong Exponential Substitution Abstract Machine without Erasure (SESAME) described in the paper \"IMELL Cut Elimination with Linear Overhead\" by B. Accattoli and C. Sacerdoti Coen, submitted at FSCD 2024.")
 (depends ocaml dune)
 (tags
  (topics IMELL "reduction machine" "linear overhead")))
