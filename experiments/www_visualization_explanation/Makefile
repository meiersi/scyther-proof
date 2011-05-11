# Purpose: Explain the workings of 'scyther-proof' with several visualzations
#          of well-known protocols.
# Author:  Simon Meier <simon.meier@inf.ethz.ch>
# Date:    July 1st, 2010
#

OUTPUT_REUSE=output/reuse
OUTPUT_NOREUSE=output/noreuse
OUTPUT_NOREUSE_FIRST=output/noreuse_first

NS3=protos/NSPK3.spthy
NSL3=protos/NSLPK3.spthy
NSL=protos/NSLPK.spthy
CR_paper=protos/CR_paper.spthy
TLS=protos/TLS.spthy
KerberosV=protos/KerberosV.spthy
Yahalom2=protos/Yahalom2.spthy

FLAGS=--isabelle --html
REUSE_FLAGS=--shortest $(FLAGS) -O$(OUTPUT_REUSE)
FIRST_FLAGS=--first $(FLAGS) -O$(OUTPUT_REUSE)
NOREUSE_FLAGS=--no-reuse --shortest $(FLAGS) -O$(OUTPUT_NOREUSE)
NOREUSE_FIRST_FLAGS=--no-reuse --first $(FLAGS) -O$(OUTPUT_NOREUSE_FIRST)

all: cr_paper nspk3 nslpk3 nslpk bigger

# three message version of NSPK with attack
cr_paper: cr_paper-reuse cr_paper-no-reuse

cr_paper-reuse: $(CR_paper)
	scyther-proof $(CR_paper) $(REUSE_FLAGS)

cr_paper-no-reuse: $(CR_paper)
	scyther-proof $(CR_paper) $(NOREUSE_FLAGS)

# three message version of NSPK with attack
nspk3: nspk3-attack

nspk3-attack: $(NS3)
	scyther-proof $(NS3) $(REUSE_FLAGS)

# three message version of NSLPK
nslpk3: nslpk3-reuse nslpk3-no-reuse nslpk3-no-reuse-first

nslpk3-reuse: $(NSL3)
	scyther-proof $(NSL3) $(REUSE_FLAGS)

nslpk3-no-reuse: $(NSL3)
	scyther-proof $(NSL3) $(NOREUSE_FLAGS)

nslpk3-no-reuse-first: $(NSL3)
	scyther-proof $(NSL3) $(NOREUSE_FIRST_FLAGS)

# full version of NSLPK
# nslpk: nslpk-reuse nslpk-no-reuse  <- certificate checking takes too long for nslpk-no-reuse
nslpk: nslpk-reuse

nslpk-reuse: $(NSL)
	scyther-proof $(NSL) $(REUSE_FLAGS)

nslpk-no-reuse: $(NSL)
	scyther-proof $(NSL) $(NOREUSE_FLAGS)

# bigger examples
bigger: tls-reuse kerberosV-reuse yahalom2-reuse

tls-reuse: $(TLS)
	scyther-proof $(TLS) $(REUSE_FLAGS)

kerberosV-reuse: $(KerberosV)
	scyther-proof $(KerberosV) $(REUSE_FLAGS)

yahalom2-reuse: $(Yahalom2)
	scyther-proof $(Yahalom2) $(REUSE_FLAGS)

# cleanup
clean:
	rm -rf $(OUTPUT_REUSE)
	rm -rf $(OUTPUT_NOREUSE)
	rm -rf $(OUTPUT_NOREUSE_FIRST)
