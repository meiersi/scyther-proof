# Purpose: Makefile for generating the data underlying our paper 
#           
#             "Strong Invariants for Interactive and Automatic Security Protocol Verification"
#
# Author: 
# Creation Date: 2010/01/18

REPORT=results.txt
OUTPUT=output

# timeout in seconds (0 for no timeout)
TIMEOUT=0

# the basic call of scytherP  
#   - soundness check is disabled because it is done by Isabelle
#   - hide=auto means that automatically generated properties (except weak
#     atomicity) which are NOT referenced by the properties of interest are not
#     output in the certificate.
SCYTHERP=scytherP --report=$(REPORT) --ASCII --timeout=$(TIMEOUT) --no-soundness-check --hide=auto

# input set
#########################################

# all protocols
INPUT=protocols/comparison_Isabelle_OFMC/Andrew.spthy protocols/comparison_Isabelle_OFMC/Bilateral-Key_Exchange.spthy protocols/comparison_Isabelle_OFMC/Denning-Sacco.spthy protocols/comparison_Isabelle_OFMC/nsl.spthy protocols/comparison_Isabelle_OFMC/tls-simplified.spthy protocols/comparison_Isabelle_OFMC/WideMouthFrog.spthy protocols/auto_properties/Yahalom2.spthy protocols/auto_properties/TLS_paulson.spthy protocols/auto_properties/KerberosV_autoprops.spthy protocols/clean/KerberosV.spthy

# additional parameters
#######################


SHORTEST_REUSE=$(SCYTHERP) --shortest --Output=$(OUTPUT)_SR $(INPUT)


# report generation
###################

all: 
	$(SHORTEST_REUSE) --isabelle 
	# --isabelle-threads=1

