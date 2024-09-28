this folder contains the two implementations of the karatsuba multiplier,
1. combinational : in the file `combinational_karatsuba.v`
2. sequential :    in the file `karatsuba_sequential.v`

to create a executable, make sure to have `iverilog` installed and then run 

$ iverilog <filename> -o <exec-name>

test benches for the files are already included in the files
