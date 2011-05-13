
# Generation, checking, and visualization of security proofs for the
# authentication protocols from the ISO/IEC-9798 standard, as described in
# Basin, Cremers, Meier. "Provably Repairing the ISO/IEC 9798 Standard for
# Entity Authentication". 2011. to be published.
#
# Requirements: 
#   - GraphViz (for the visualization)
#   - Isabelle2009-1 (http://isabelle.in.tum.de/index.html)
#   - newest scyther-proof with Isabelle support 
#     (build according to: https://svn.inf.ethz.ch/svn/basin/infsec/trunk/projects/FOSSP/espl/README)

iso9798-generate-proofs:
	scyther-proof iso9798/*.spthy --shortest -Oiso9798/isabelle-proofs --ASCII

iso9798-generate-and-check-proofs:
	scyther-proof iso9798/*.spthy --shortest -Oiso9798/isabelle-proofs --isabelle

iso9798-generate-check-and-visualize-proofs:
	scyther-proof iso9798/*.spthy --shortest -Oiso9798/proofs-visualized --isabelle --html

iso9798-visualize-proofs:
	scyther-proof iso9798/*.spthy --shortest -Oiso9798/proofs-visualized --html

iso9798-generate-parallel-proofs:
	scyther-proof iso9798/*.spthy --compose-parallel --shortest -Oiso9798/isabelle-parallel-proofs --ASCII
	
iso9798-generate-and-check-parallel-proofs:
	scyther-proof iso9798/*.spthy --compose-parallel --shortest -Oiso9798/isabelle-parallel-proofs --isabelle

iso9798-generate-check-and-visualize-parallel-proofs:
	scyther-proof iso9798/*.spthy --compose-parallel --shortest -Oiso9798/parallel-proofs-visualized --isabelle --html

iso9798-visualize-parallel-proofs:
	scyther-proof iso9798/*.spthy --compose-parallel --shortest -Oiso9798/parallel-proofs-visualized --html
	
