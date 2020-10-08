rm -f out/tnf_asm.*
time swipl -s tnf.pro -g "run_orig('progs/$1.pro'),halt"
time swipl -s tnf.pro -g "run('progs/$1.pro'),halt"
time python3 -O tnf.py
