# Regression test: checking standard examples.

check-all: check-classic check-spore iso9798-generate-and-check-proofs iso9798-generate-and-check-parallel-proofs

check-classic:
	scyther-proof classic/*.spthy --shortest -Oclassic/isabelle-proofs --ASCII --isabelle

check-spore:
	scyther-proof spore/*.spthy --shortest -Ospore/isabelle-proofs --ASCII --isabelle


# Case studies for the journal version: Meier, Cremers, Basin. "Efficient
# Construction of Symbolic Protocol Security Proofs". 2011. to be published.

CASESTUDY_IN  = spore/Lowe_modified_BAN_concrete_Andrew_Secure_RPC.spthy spore/Woo_Lam_Pi_3.spthy spore/Amended_Needham_Schroeder_Symmetric_Key.spthy spore/Lowe_fixed_Needham_Schroeder_Public_Key.spthy spore/Paulson_strengthened_Yahalom.spthy spore/Lowe_modified_Denning_Sacco_shared_key.spthy spore/BAN_modified_CCITT_X509_3.spthy spore/Kerberos_V5.spthy classic/Kerberos_V4.spthy classic/TLS.spthy
CASESTUDY_OUT = case_study_out

case-studies-journal:
	scyther-proof $(CASESTUDY_IN) -O$(CASESTUDY_OUT) --no-reuse --shortest

case-studies-journal-html:
	scyther-proof $(CASESTUDY_IN) --shortest -O$(CASESTUDY_OUT) --isabelle --html

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
	
