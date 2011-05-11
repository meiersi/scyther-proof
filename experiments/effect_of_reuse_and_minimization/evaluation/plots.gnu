# set terminal png transparent nocrop enhanced font arial 8 size 420,320 
# set output 'generation_time.png'

set terminal svg

# set terminal x11 persist

# set boxwidth 0.9 absolutee
set palette gray
set style fill solid 0.90 border -1 
set style histogram clustered gap 1 title  offset character 0, 0, 0
set datafile missing '-'
set style data histograms
set logscale y 10
set xtics border in scale 1,0.5 nomirror rotate by -45  offset character -1, -0.2, 0 
set yrange [ 0.5 : 400 ] noreverse nowriteback
set key left

set output 'generation_time.svg'
set title "Generation time relative to generating the minimal proof with reuse." 
plot 'generation_time.dat' using ($3/$2):xtic(1) ti col, '' using ($4/$2) ti col, '' using ($5/$2) ti col

set output 'checking_time.svg'
set title "Checking time relative to checking the minimal proof with reuse." 
plot 'checking_time.dat' using ($3/$2):xtic(1) ti col, '' using ($4/$2) ti col, '' using ($5/$2) ti col

set yrange [ 0.001 : 100 ] noreverse nowriteback

set output 'absolute_generation_time.svg'
set title "Generation time in seconds" 
plot 'generation_time.dat' using ($2):xtic(1) ti col, '' using ($3) ti col, '' using ($4) ti col, '' using ($5) ti col

set yrange [ 5 : 10000 ] noreverse nowriteback

set output 'absolute_checking_time.svg'
set title "Checking time in seconds" 
plot 'checking_time.dat' using ($2):xtic(1) ti col, '' using ($3) ti col, '' using ($4) ti col, '' using ($5) ti col

####################
# combined time plot
####################

set terminal svg size 600,700 dynamic

set output 'absolute_time_combined.svg'
unset title
set multiplot layout 2, 1 scale 1,1

set title "Generation time in seconds" 
set yrange [ 0.001 : 100 ] noreverse nowriteback
# unset tics
# set ytics border
plot 'generation_time.dat' using ($2):xtic(1) ti col, '' using ($3) ti col, '' using ($4) ti col, '' using ($5) ti col

set title "Checking time in seconds" 
set yrange [ 5 : 10000 ] noreverse nowriteback
# set xtics border in scale 1,0.5 nomirror rotate by -45  offset character -1, -0.2, 0 
plot 'checking_time.dat' using ($2):xtic(1) ti col, \
     ''                  using ($3) ti col , \
     ''                  using ($4) ti col, \
     ''                  using ($5) ti col

unset multiplot
