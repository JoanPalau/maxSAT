#!bin/bash
# Author: Joan Palau Oncins
#
# Aquest script executa tots els tests de la carpeta situada a
# ia-prac2/graphs
# per tal de millorar el temps de comput, s'executen els test en
# segon pla i els resultats són emmagatzemats a un fitxer .txt

graphdir="ia-prac2/graphs/"
srcdir="ia-prac2/src/"

    for file in $(ls $graphdir); do
        name=$(basename ${file%.*})
        { time python3 $srcdir"graph.py" -n -1 $srcdir"WPM1-2012" $graphdir$file; } &> results/$name"Sol.txt" &
    done
exit 0