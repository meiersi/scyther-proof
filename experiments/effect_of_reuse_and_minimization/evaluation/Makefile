
all: absolute_time_combined.pdf

absolute_time_combined.pdf: plots.gnu checking_time.dat generation_time.dat
	gnuplot plots.gnu
	inkscape absolute_time_combined.svg --export-pdf=absolute_time_combined.pdf

