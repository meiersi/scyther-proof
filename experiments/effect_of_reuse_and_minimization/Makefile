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

# the basic call of scytherP  (soundness check is disabled because it is done by Isabelle)
SCYTHERP=scytherP --report=$(REPORT) --ASCII --timeout=$(TIMEOUT) --no-soundness-check --hide=auto

# input sets for the different parameters
#########################################

# all protocols
INPUT_SR=protocols/BKE.spthy protocols/CR_paper.spthy protocols/DenningSacco.spthy protocols/NS_Public.spthy protocols/OtwayRees.spthy protocols/TLS.spthy protocols/WMF.spthy protocols/Yahalom2.spthy protocols/WooLam.spthy protocols/KerberosV.spthy 

# no kerberos and no woolam because ealier measurements show that they take longer than 5 hours
INPUT_SN=protocols/BKE.spthy protocols/CR_paper.spthy protocols/DenningSacco.spthy protocols/NS_Public.spthy protocols/OtwayRees.spthy protocols/TLS.spthy protocols/WMF.spthy protocols/Yahalom2.spthy

# removed KerberosV because it takes too long for checking
INPUT_FR=protocols/BKE.spthy protocols/CR_paper.spthy protocols/DenningSacco.spthy protocols/NS_Public.spthy protocols/OtwayRees.spthy protocols/TLS.spthy protocols/WMF.spthy protocols/Yahalom2.spthy protocols/WooLam.spthy

# removed KerberosV due to out of memory bound when writing the file
# removd WooLam from checking because it didn't terminate after 15h
INPUT_FN=protocols/BKE.spthy protocols/CR_paper.spthy protocols/DenningSacco.spthy protocols/NS_Public.spthy protocols/OtwayRees.spthy protocols/TLS.spthy protocols/WMF.spthy protocols/Yahalom2.spthy

# parameters sets
#################


SHORTEST_REUSE=$(SCYTHERP) --shortest --Output=$(OUTPUT)_SR $(INPUT_SR)
# the no-minimize flag is OK for SHORTEST_NOREUSE because there won't be any forward resolutions anyways
SHORTEST_NOREUSE=$(SCYTHERP) --shortest --no-reuse --no-minimize --Output=$(OUTPUT)_SN $(INPUT_SN)
FIRST_REUSE=$(SCYTHERP) --first --no-minimize --Output=$(OUTPUT)_FR $(INPUT_FR)
FIRST_NOREUSE=$(SCYTHERP) --first --no-reuse --no-minimize --Output=$(OUTPUT)_FN $(INPUT_FN)


# report generation
###################

generate: 
	$(SHORTEST_REUSE) 
	$(SHORTEST_NOREUSE)
	$(FIRST_REUSE) protocols/KerberosV.spthy  # added KerberosV because generation works
	$(FIRST_NOREUSE) protocols/WooLam.spthy # added WooLam because generation works

check:
	$(SHORTEST_REUSE) --isabelle --no-generation
	$(SHORTEST_NOREUSE) --isabelle --no-generation protocols/WooLam.spthy protocols/KerberosV.spthy  # managed to generate them with > 5 and > 15 hours
	$(FIRST_REUSE) --isabelle --no-generation
	$(FIRST_NOREUSE) --isabelle --no-generation

all: check generate

clean:
	rm -f results.txt
	rm -rf output
