# GNU Makefile for ScytherP and the Isabelle Embedded Security Protocol Logic
#
# Author: Simon Meier <simon.meier@inf.ethz.ch>
# Date:   13.1.2010
# Modified: 23.6.2010 - Renaming of scytherP to scyther-proof 



# The following commands require
#
#   a working GHC installation (tested with GHC 6.12.1)
#   cabal-install (http://hackage.haskell.org/package/cabal-install)
#
# The easiest way to satisfy these requirements is to install the Haskell
# Platform (http://hackage.haskell.org/platform/).
#

# install the 'scyther-proof' executable.
scyther-proof-install:
	cd ScytherP; cabal install

# build the developer documentation (see the console output for its location).
scyther-proof-doc:
	cd ScytherP; cabal haddock --executables


# The following commands require
#
#   a working installation of Isabelle2013
#   (http://www.cl.cam.ac.uk/research/hvg/Isabelle/).
#

# build an image of the ESPL formalization in Isabelle. This is required for
# the 'scyther-proof --isabelle' switch to work.
espl-image:
	isabelle build -cb -d . ESPL
