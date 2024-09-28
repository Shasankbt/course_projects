module multiplier_2bit(
    input wire [1:0] x,
    input wire [1:0] y,
    output wire [3:0] m
);

    wire m00, m01, m10, m11, m01_10;
    assign m00 = x[0] & y[0];
    assign m01 = x[0] & y[1];
    assign m10 = x[1] & y[0];
    assign m11 = x[1] & y[1];
    assign m01_10 = m10 & m01;

    assign m[0] = m00;
    assign m[1] = (m01 ^ m10);
    assign m[2] = (m11 & ~m01_10);
    assign m[3] = m11 & m01_10;
endmodule

module CLA_4bit(a, b, cin, sum, cout);
    input wire[3:0] a, b;
    input wire cin;
    output wire[3:0] sum;
    output wire cout;


    wire[3:0] P, G;
    wire[4:0] carry_connecters;
    
    generate
        genvar i;
        for(i=0;i<4;i=i+1) begin
            assign P[i] = a[i] ^ b[i];
            assign G[i] = a[i] & b[i];
            assign sum[i] = P[i] ^ carry_connecters[i];
        end
    endgenerate

    assign carry_connecters[0] = cin;
    assign carry_connecters[1] = G[0] | (P[0] & cin);
    assign carry_connecters[2] = G[1] | (G[0] & P[1]) | (P[1] & P[0] & cin);
    assign carry_connecters[3] = G[2] | (P[2] & G[1]) | (P[2] & P[1] & G[0]) | (P[2] & P[1] & P[0] & cin);
    assign carry_connecters[4] = G[3] | (P[3] & G[2]) | (P[3] & P[2] & G[1]) | (P[3] & P[2] & P[1] & G[0]) | (P[3] & P[2] & P[1] & P[0] & cin);
    assign cout = carry_connecters[4];

endmodule 

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

module adder #(parameter N = 4) (
    input wire[N-1:0] a,
    input wire[N-1:0] b,
    input wire cin,
    output wire[N-1:0] sum,
    output wire cout
);
    generate
        if(N == 4) begin 
            CLA_4bit U0 (
                .a(a), .b(b), .cin(cin), .cout(cout), .sum(sum)
            );
        end else begin 
            localparam half = N/2;
            wire interim_carry;
            adder #(half) U0(.a(a[half-1:0]), .b(b[half-1:0]), .cin(cin), .sum(sum[half-1:0]), .cout(interim_carry));
            adder #(half) U1(.a(a[N-1:half]), .b(b[N-1:half]), .cin(interim_carry), .sum(sum[N-1:half]), .cout(cout));
        end
    endgenerate
endmodule

module middle_block #(parameter N=4)(
    input wire [N-1:0]x,
    input wire [N-1:0] y,
    output wire [N-1:0] middlesum,
    output wire carryout
);
    // this returns the value of (x0+x1)*(y0+y1) where x0 and x1 are the first half and second half bits in x
    // although the output requires N+2 bits, we only give N (output) + 1(carryout) since in the grand sceme, 
    // x0*y1 + x1*y0 contains N + 1 bits so the most significant bit of (x0+y0)*(x1+y1) can be ignored ;)

    localparam half = N/2;
    // concatenating bits x0 + x1 and y0 + y1
    wire[N-1:0] concat1, concat2;
    adder #(N) U0(
        .a({{half{1'b0}}, x[N-1:half]}),
        .b({{half{1'b0}}, x[half-1:0]}),
        .cin(1'b0),
        .sum(concat1)
    );
    adder #(N) U1(
        .a({{half{1'b0}},y[N-1:half]}),
        .b({{half{1'b0}}, y[half-1:0]}),
        .cin(1'b0),
        .sum(concat2)
    );
    // mutliplying concatenated digits (except carry)
    wire[N-1:0] middle_product;
    karatsuba #(half) U2(
        .x(concat1[half-1:0]),
        .y(concat2[half-1:0]),
        .m(middle_product)
    );
    // checking if digits needed to be added based on carry
    wire[N-1:0] enabled_concat1, enabled_concat2, enabled_sum;
    enabler #(N) U3 (.in({{half{1'b0}}, concat1[half-1:0]}), .enable(concat2[half]), .out(enabled_concat1));
    enabler #(N) U4 (.in({{half{1'b0}}, concat2[half-1:0]}), .enable(concat1[half]), .out(enabled_concat2));
    // calculating extra sum (with carry excluding main (above))
    adder #(N) U5(
        .a(enabled_concat1),
        .b(enabled_concat2),
        .cin(1'b0),
        .sum(enabled_sum)
    );
    // combining both
    wire tempcarry;
    adder #(N) U6(
        .a(middle_product),
        .b({enabled_sum[half-1:0], {half{1'b0}}}),
        .cin(1'b0),
        .sum(middlesum),
        .cout(tempcarry)
    );
    assign carryout = enabled_sum[half] ^ tempcarry ^ (concat1[half] & concat2[half]);
endmodule

module karatsuba #(parameter N = 2)(
    input wire [N-1:0] x,
    input wire [N-1:0] y,
    output wire [2*N-1:0] m
);
    generate
        if(N==2) begin 
            multiplier_2bit U0(
                .x(x), .y(y), .m(m)
            );
        end else begin
            localparam half = N/2;
            wire[N-1:0] m00, m11;
            karatsuba #(N/2) U0(.x(x[half-1:0]), .y(y[half-1:0]), .m(m00));
            karatsuba #(N/2) U1(.x(x[N-1:half]), .y(y[N-1:half]), .m(m11));

            
            //middle adder : gives `middle_interim_sum` and `middle_interim_carry`

            // calculating x0 * y0 + x1 * y1 = m00 + m11 
            wire[N:0] exterior_prod_sum; 
            adder #(N) U2 (
                .a(m00),
                .b(m11), 
                .cin(1'b0), 
                .sum(exterior_prod_sum[N-1:0]), 
                .cout(exterior_prod_sum[N]) // the carry is also stored in the sum
            );
            // calculating (x0+x1)*(y0+y1) using the middle block module defined above
            wire[N:0] concat_prod;
            middle_block #(N) U3 (
                .x(x),
                .y(y),
                .middlesum(concat_prod[N-1:0]),
                .carryout(concat_prod[N])   // the carry is also stored in the prod var
            );
            // subtracting m00 + m11 from (x0+x1)*(y0+y1) by the (m00 + m11)-compliment
            wire[N-1:0] middle_interem_sum; // x0 * y1 + x1 * y0
            wire temp_subt_carry, middle_interem_carry;
            adder #(N) U4 (
                .a(concat_prod[N-1:0]),
                .b(~exterior_prod_sum[N-1:0]),
                .cin(1'b1),
                .sum(middle_interem_sum),
                .cout(temp_subt_carry)
            );
            assign middle_interem_carry = ~exterior_prod_sum[N] ^ temp_subt_carry ^ concat_prod[N];
            

            wire tail_interem_carry;
            adder #(N) U5 (
                .a(m00),
                .b({ middle_interem_sum[half-1:0] , {half{1'b0}} }),
                .cin(1'b0),
                .sum(m[N-1:0]),
                .cout(tail_interem_carry)
            );  // tail adder
            adder #(N) U6 (
                .a(m11),
                .b({ {(half-1){1'b0}} , middle_interem_carry , middle_interem_sum[N-1:half] }),
                .cin(tail_interem_carry),
                .sum(m[2*N-1:N])
            );  // front adder
        end
    endgenerate
endmodule

module karatsuba_16 (X, Y, Z);
    input wire[15:0] X, Y;
    output wire[31:0] Z;
    karatsuba #(16) U0 (.x(X), .y(Y), .m(Z));
endmodule

`timescale 1ns/1ps

module tb_combinational_karatsuba;

    parameter N = 16;

    reg [15:0] X, Y;
    wire [31:0] Z;

    initial begin
        
        $display("roll no: 23b1015 ; name: Shasank Reddy P ; Question-3");
        $dumpfile("combinational_karatsuba.vcd");
        $dumpvars(0, tb_combinational_karatsuba);
        $display("___________________________________________________________________________________________________");
        $display("___________X____________ | ___________Y____________ | _____________________Z_______________________");
        $display("_____binary______;__d___ | _____binary______;__d___ | _____________binary______________;_____d_____");
        $monitor("%b ; %d | %b ; %d | %b ; %d", X,X, Y,Y, Z,Z);

        // in hexadecimal [ didn't have the sanity to write in binary ;) ]
        X = 16'h0000; Y = 16'h0000; #10;
        X = 16'h0001; Y = 16'h0001; #10;
        X = 16'h0002; Y = 16'h0002; #10;
        X = 16'h000F; Y = 16'h000F; #10;
        X = 16'h00FF; Y = 16'h00FF; #10;
        X = 16'h0F0F; Y = 16'h0F0F; #10;
        X = 16'h1234; Y = 16'h5678; #10;
        X = 16'hFFFF; Y = 16'hFFFF; #10;
        
        $finish;

    end

    karatsuba_16 dut (.X(X), .Y(Y), .Z(Z));


endmodule

