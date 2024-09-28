/* 32-bit simple karatsuba multiplier */

/*32-bit Karatsuba multipliction using a single 16-bit module*/

module iterative_karatsuba_32_16(clk, rst, enable, A, B, C);
    input clk;
    input rst;
    input [31:0] A;
    input [31:0] B;
    output [63:0] C;
    input enable;
    
    
    wire [1:0] sel_x;
    wire [1:0] sel_y;
    
    wire [1:0] sel_z;
    wire [1:0] sel_T;
    
    wire en_z;
    wire en_T;
    
    
    wire [32:0] h1;
    wire [32:0] h2;
    wire [63:0] g1;
    wire [63:0] g2;
    
    assign C = g2;
    assign debug = g2;
    reg_with_enable #(.N(63)) Z(.clk(clk), .rst(rst), .en(en_z), .X(g1), .O(g2) );  // Fill in the proper size of the register
    reg_with_enable #(.N(32)) T(.clk(clk), .rst(rst), .en(en_T), .X(h1), .O(h2) );  // Fill in the proper size of the register
    
    iterative_karatsuba_datapath dp(.clk(clk), .rst(rst), .X(A), .Y(B), .Z(g2), .T(h2), .sel_x(sel_x), .sel_y(sel_y), .sel_z(sel_z), .sel_T(sel_T), .en_z(en_z), .en_T(en_T), .done(done), .W1(g1), .W2(h1));
    iterative_karatsuba_control control(.clk(clk),.rst(rst), .enable(enable), .sel_x(sel_x), .sel_y(sel_y), .sel_z(sel_z), .sel_T(sel_T), .en_z(en_z), .en_T(en_T), .done(done));
    
endmodule

/* my own created modules */
module enabler #(parameter N=4)(
    input wire [N-1:0] in,
    input wire enable,
    output wire [N-1:0] out
    );
    generate
        genvar i;
        for(i=0;i<N;i=i+1) 
            assign out[i] = in[i] & enable;
    endgenerate
endmodule

module mult_16bit_extra(
    input wire [16:0] x,
    input wire [16:0] y,
    output wire [32:0] z
);
    // this is an extension of a 16 bit mtheultiplier in where the inputs are 17 bits
    // the output is the last 33 bits of the product

    wire[31:0] main_prod;
    wire[15:0] enabled_sub_x, enabled_sub_y, enabled_sum;
    wire enabled_carry;
    mult_16 U0(.X(x[15:0]), .Y(y[15:0]), .Z(main_prod));  

    enabler #(16) U1 (.in(x[15:0]), .enable(y[16]), .out(enabled_sub_x));
    enabler #(16) U2 (.in(y[15:0]), .enable(x[16]), .out(enabled_sub_y));  
    adder_Nbit #(.N(16)) U3 (
        .a(enabled_sub_x),
        .b(enabled_sub_y),
        .cin(1'b0),
        .S(enabled_sum),
        .cout(enabled_carry));

    wire tempcout;
    adder_Nbit #(.N(32)) U4 (
        .a(main_prod),
        .b({enabled_sum, 16'b0}),
        .cin(1'b0), .S(z[31:0]),
        .cout(tempcout)
    );
    assign z[32] = (x[16] & y[16]) ^ tempcout ^ enabled_carry;
endmodule

module iterative_karatsuba_datapath(clk, rst, X, Y, T, Z, sel_x, sel_y, en_z, sel_z, en_T, sel_T, done, W1, W2);
    input clk;
    input rst;
    input [31:0] X;    // input X
    input [31:0] Y;    // Input Y
    input [32:0] T;    // input which sums X_h*Y_h and X_l*Y_l (its also a feedback through the register)
    input [63:0] Z;    // input which calculates the final outcome (its also a feedback through the register)
    output reg [63:0] W1;  // Signals going to the registers as input
    output reg [32:0] W2;  // signals hoing to the registers as input
    
    input [1:0] sel_x;  // control signal 
    input [1:0] sel_y;  // control signal 
    
    input en_z;         // control signal 
    input [1:0] sel_z;  // control signal 
    input en_T;         // control signal 
    input [1:0] sel_T;  // control signal 
    
    input done;         // Final done signal
    
    // multiplier, the regs here are just a representation of a mux that could have been used
    // states used : 0, 1, 2
    reg [16:0] mul_in_1, mul_in_2;
    wire [32:0] mul_out;
    mult_16bit_extra U0 (
        .x(mul_in_1), .y(mul_in_2), .z(mul_out)
    );

    // small 32 bit adder for xh + xl and zh + zl calculation
    // states used : 2, 3
    reg [31:0] small_adder_in_1, small_adder_in_2;
    wire [31:0] small_adder_out;
    wire small_adder_cout;
    adder_Nbit #(.N(32)) U1 (
        .a(small_adder_in_1), .b(small_adder_in_2), .cin(1'b0), .S(small_adder_out), .cout(small_adder_cout)
    );

    // big 48 bit adder used for yh + yl and Zmiddle + T calculation
    // states used : 2 , 3
    reg [47:0] big_adder_in_1, big_adder_in_2;
    wire [47:0] big_adder_out;
    wire big_adder_cout;
    adder_Nbit #(.N(48)) U2 (
        .a(big_adder_in_1), .b(big_adder_in_2), .cin(1'b0), .S(big_adder_out), .cout(big_adder_cout)
    );

    // 33 bit subtractor used to calculate (xh + xl) * (yh + yl) - (xh*yh + xl*yl)
    // states used : 4
    wire [32:0] subtract_out;
    subtract_Nbit #(.N(33)) U3 (
        .a(T), .b({small_adder_cout , small_adder_out}), .S(subtract_out)
    );

    // always @ (posedge clk) begin 
    //     $display("stage: %b  Z:%b ; T: %b; subout : %b",sel_x,   Z, T, subtract_out);
    // end

    always @ * begin
        case(sel_x)
            2'b01: begin // state 0
                mul_in_1 <= { 1'b0 , X[15:0] };
                mul_in_2 <= { 1'b0 , Y[15:0] };
                W1 <= { 32'b0 , mul_out[31:0] };
            end
            2'b10: begin// state 1
                mul_in_1 <= { 1'b0 , X[31:16] };
                mul_in_2 <= { 1'b0 , Y[31:16] };
                W1 <= { mul_out[31:0] , Z[31:0] };
            end
            2'b11: begin// state 2
                // for (xh + xl) * (yh + yl);
                small_adder_in_1 <= { 16'b0 , X[15:0] };
                small_adder_in_2 <= { 16'b0 , X[31:16] };
                big_adder_in_1 <= { 32'b0 , Y[15:0] };
                big_adder_in_2 <= { 32'b0 , Y[31:16] };
                mul_in_1 <= big_adder_out[16:0];
                mul_in_2 <= small_adder_out[16:0];
                W2 <= mul_out;
            end
            2'b00: begin 
                small_adder_in_1 <= Z[31:0];
                small_adder_in_2 <= Z[63:32];
                big_adder_in_1 <= { 15'b0 , subtract_out };
                big_adder_in_2 <= Z[63:16];
                W1 <= { big_adder_out , Z[15:0] };
            end
            default: begin 
                mul_in_1 <= 17'b0;
                mul_in_2 <= 17'b0;
                small_adder_in_1 <= 32'b0;
                small_adder_in_2 <= 32'b0;
                big_adder_in_1 <= 48'b0;
                big_adder_in_2 <= 48'b0;
            end
        endcase
    end

endmodule

module iterative_karatsuba_control(clk,rst, enable, sel_x, sel_y, sel_z, sel_T, en_z, en_T, done);
    input clk;
    input rst;
    input enable;
    
    output reg [1:0] sel_x;
    output reg [1:0] sel_y;
    
    output reg [1:0] sel_z;
    output reg [1:0] sel_T;    
    
    output reg en_z;
    output reg en_T;
    
    
    output reg done;
    
    reg [5:0] state, nxt_state;
    parameter emptystage = 6'b000001;   // initial state
    parameter S0 = 6'b000010;   
    parameter S1 = 6'b000100;
    parameter S2 = 6'b001000;
    parameter S3 = 6'b010000;
    parameter endstage = 6'b100000;

    always @(posedge clk) begin
        if (rst) begin
            state <= emptystage;
        end
        else if (enable) begin
            state <= nxt_state;
        end
    end
    
    always@(*) begin
        case(state) 
            emptystage:
                begin
				    sel_x = 2'b00; sel_y = 2'b00;
                    en_z = 1'b0;   en_T = 1'b0;
                    sel_z = 2'b00; sel_T = 2'b00;
                    done = 1'b0;

                    nxt_state = S0;
                end 
            S0: 
                begin
                    sel_x = 2'b01;  sel_y = 2'b01;
                    en_z = 1'b1;    en_T = 1'b0;
                    sel_z = 2'b00;  sel_T = 2'b00;
                    
                    done = 1'b0;    nxt_state = S1;
                end
            S1: 
                begin
                    sel_x = 2'b10;  sel_y = 2'b10;
                    en_z = 1'b1;    en_T = 1'b0;
                    sel_z = 2'b00;  sel_T = 2'b00;
                    
					nxt_state = S2;
                end
            S2: 
                begin
                    sel_x = 2'b11;  sel_y = 2'b00;
                    en_z = 1'b0;    en_T = 1'b1;
                    sel_z = 2'b00;  sel_T = 2'b00;
                    
					nxt_state = S3;
                end
            S3: 
                begin
                    sel_x = 2'b00;  sel_y = 2'b11;
                    en_z = 1'b1;    en_T = 1'b0;
                    sel_z = 2'b00;  sel_T = 2'b01;
                    
					nxt_state = endstage;
                end
            endstage:
                begin
                    en_z = 1'b0;    en_T = 1'b0;
                    
                    done = 1'b1;
                end
            default: 
                begin
				    sel_x = 2'b00; sel_y = 2'b00;
                    en_z = 1'b0;   en_T = 1'b0;
                    sel_z = 2'b00; sel_T = 2'b00;

                    done = 1'b0;
                end            
        endcase
        
    end

endmodule


module reg_with_enable #(parameter N = 32) (clk, rst, en, X, O );
    input [N:0] X;
    input clk;
    input rst;
    input en;
    output [N:0] O;
    
    reg [N:0] R;
    
    always@(posedge clk) begin
        if (rst) begin
            R <= {N{1'b0}};
        end
        if (en) begin
            R <= X;
        end
    end
    assign O = R;
endmodule



/*-------------------Supporting Modules--------------------*/


module mult_16(X, Y, Z);
input [15:0] X;
input [15:0] Y;
output [31:0] Z;

assign Z = X*Y;

endmodule


module mult_17(X, Y, Z);
input [16:0] X;
input [16:0] Y;
output [33:0] Z;

assign Z = X*Y;

endmodule

module full_adder(a, b, cin, S, cout);
input a;
input b;
input cin;
output S;
output cout;

assign S = a ^ b ^ cin;
assign cout = (a&b) ^ (b&cin) ^ (a&cin);

endmodule


module check_subtract (A, B, C);
 input [7:0] A;
 input [7:0] B;
 output [8:0] C;
 
 assign C = A - B; 
endmodule



/* N-bit RCA adder (Unsigned) */
module adder_Nbit #(parameter N = 32) (a, b, cin, S, cout);
input [N-1:0] a;
input [N-1:0] b;
input cin;
output [N-1:0] S;
output cout;

wire [N:0] cr;  

assign cr[0] = cin;


generate
    genvar i;
    for (i = 0; i < N; i = i + 1) begin
        full_adder addi (.a(a[i]), .b(b[i]), .cin(cr[i]), .S(S[i]), .cout(cr[i+1]));
    end
endgenerate    


assign cout = cr[N];

endmodule


module Not_Nbit #(parameter N = 32) (a,c);
input [N-1:0] a;
output [N-1:0] c;

generate
genvar i;
for (i = 0; i < N; i = i+1) begin
    assign c[i] = ~a[i];
end
endgenerate 

endmodule


/* 2's Complement (N-bit) */
module Complement2_Nbit #(parameter N = 32) (a, c, cout_comp);

input [N-1:0] a;
output [N-1:0] c;
output cout_comp;

wire [N-1:0] b;
wire ccomp;

Not_Nbit #(.N(N)) compl(.a(a),.c(b));
adder_Nbit #(.N(N)) addc(.a(b), .b({ {N-1{1'b0}} ,1'b1 }), .cin(1'b0), .S(c), .cout(ccomp));

assign cout_comp = ccomp;

endmodule


/* N-bit Subtract (Unsigned) */
module subtract_Nbit #(parameter N = 32) (a, b, cin, S, ov, cout_sub);

input [N-1:0] a;
input [N-1:0] b;
input cin;
output [N-1:0] S;
output ov;
output cout_sub;

wire [N-1:0] minusb;
wire cout;
wire ccomp;

Complement2_Nbit #(.N(N)) compl(.a(b),.c(minusb), .cout_comp(ccomp));
adder_Nbit #(.N(N)) addc(.a(a), .b(minusb), .cin(1'b0), .S(S), .cout(cout));

assign ov = (~(a[N-1] ^ minusb[N-1])) & (a[N-1] ^ S[N-1]);
assign cout_sub = cout | ccomp;

endmodule


/* n-bit Left-shift */

module Left_barrel_Nbit #(parameter N = 32)(a, n, c);

input [N-1:0] a;
input [$clog2(N)-1:0] n;
output [N-1:0] c;


generate
genvar i;
for (i = 0; i < $clog2(N); i = i + 1 ) begin: stage
    localparam integer t = 2**i;
    wire [N-1:0] si;
    if (i == 0) 
    begin 
        assign si = n[i]? {a[N-t:0], {t{1'b0}}} : a;
    end    
    else begin 
        assign si = n[i]? {stage[i-1].si[N-t:0], {t{1'b0}}} : stage[i-1].si;
    end
end
endgenerate

assign c = stage[$clog2(N)-1].si;

endmodule

/*------------- Iterative Karatsuba: 32-bit Karatsuba using a single 16-bit Module*/

module tb_karatsuba_multiplier_32x32;
    reg clk;
    reg rst;
    reg enable;
    reg [31:0] A;
    reg [31:0] B;
    wire [63:0] C;
    wire [63:0] debug;
    wire done_out;
    
    // Instantiate the Karatsuba multiplier
    iterative_karatsuba_32_16 uut (
        .clk(clk),
        .rst(rst),
        .enable(enable),
        .A(A),
        .B(B),
        .C(C)
        
    );

    // Clock generation
    always begin
        #5 clk = ~clk; // 100MHz clock
    end

    initial begin
        // Initialize inputs
        clk = 0;
        rst = 1;
        enable = 0;
        A = 32'd0;
        B = 32'd0;

        $display("---------------------");
        enable = 0; rst = 1 ; #10 ; rst = 0; #10;
        enable = 1;
        A = 32'd64;  // 0x0000000F
        B = 32'd4;  // 0x0000000A
        
        #100;

        $display("---------------------");
        enable = 0; rst = 1 ; #10 ; rst = 0; #10;
        A = 32'd123456789;  // 0x075BCD15
        B = 32'd987654321;  // 0x3ADE68B1
        enable = 1;
        
        #100;

        $display("---------------------");
        enable = 0; rst = 1 ; #10 ; rst = 0; #10;
        A = 32'hFFFFFFFF;  // 0xFFFFFFFF
        B = 32'hFFFFFFFF;  // 0xFFFFFFFF
        enable = 1;
        
        #100;

        $display("---------------------");
        enable = 0; rst = 1 ; #10 ; rst = 0; #10;
        A = 32'h00000001;  // 0x00000001
        B = 32'h00000001;  // 0x00000001
        enable = 1;

        #100
        
        $display("---------------------");

        enable = 0; rst = 1 ; #10 ; rst = 0; #10;
        A = 32'h87654321;  // 0x87654321
        B = 32'h12345678;  // 0x12345678
        enable = 1;

        #100;

        $display("---------------------");
        enable = 0; rst = 1 ; #10 ; rst = 0; #10;
        A = 32'hAAAAAAAA;  // 0xAAAAAAAA
        B = 32'h55555555;  // 0x55555555
        enable = 1;

        #100;

        $display("---------------------");
        enable = 0; rst = 1 ; #10 ; rst = 0; #10;
        A = 32'h80000000;  // 0x80000000
        B = 32'h00000002;  // 0x00000002
        enable = 1;

        #100;

        $display("---------------------");
        enable = 0; rst = 1 ; #10 ; rst = 0; #10;
        A = 32'h12345678;  // 0x12345678
        B = 32'h87654321;  // 0x87654321
        enable = 1;

        #100;

        // // End simulation
        $finish;
    end

    // Monitor output
    initial begin
        $monitor("Time: %0t | A: %d | B: %d | enable: %b | C: %d ", $time, A, B, enable, C);
    end
endmodule



// // `timescale 1ns/1ps
// `timescale 1ns/1ps
// module tb_iterative_karatsuba;
// parameter N = 32;

// reg clk;
// reg rst;
// reg enable;

// reg [N-1:0] X;
// reg [N-1:0] Y;

// wire [(2*N - 1):0] Z;

// reg [1:0] sel_x;
// reg [1:0] sel_y;
// reg  en_xhyh;
// reg  en_xlyl;
// reg  en_inter;

// reg done;

// reg [N:0] i;
// reg [N:0] j;

// always begin
//     #5 clk = ~clk;
// end

// initial begin
//     $display("time\t, clk\t rst\t, X\t, Y\t, Z\t ");
//     $monitor ("%g\t %b\t   %b\t     %d\t      %d\t      %d\t   ", $time, clk, rst, X, Y, Z);	

//     clk = 1;
//     rst = 0;
//     enable = 0;
    
    
//     #10 rst = 1;
//     #10 rst  = 0;
    
//     //#10 X = 4294967295;
//     //    Y = 255;
//     #10 X = 10;
//         Y = 12;
//         enable = 1'b1;   
        
        
//     #50 rst = 1;
//         enable = 1'b0;
        
//     for (i=0; i<10; i=i+1) begin
//         for (j=0; j<10; j=j+1) begin
//             X = i; 
//             Y = 12;
//             enable = 1'b1; 
//             #50 
//             if (Z != X*Y) begin
//                 $display("ERROR");
//                 $monitor("%d\t", Z);
//                 $finish;
//             end 
//             #50 rst = 1;
//             enable = 1'b0;
//             #10 rst = 0;
            
//         end    
//     end                
    
//     //#10 rst = 0;
//     //#10 X = 334;
//     //    Y = 324;    
//     //    enable = 1'b1;
        
//     #100 enable = 1'b0;
    
//     #100
//     #500 $finish;
// end




// iterative_karatsuba_32_16 ik(.clk(clk), .rst(rst), .enable(enable), .A(X), .B(Y), .C(Z) );


// initial begin
//     $dumpfile("iterative_karatsuba.vcd");
//     $dumpvars(0,tb_iterative_karatsuba);
// end

// endmodule

