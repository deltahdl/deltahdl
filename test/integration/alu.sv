module alu #(parameter WIDTH = 8)(
    input  logic [WIDTH-1:0] a,
    input  logic [WIDTH-1:0] b,
    input  logic [2:0]       op,
    output logic [WIDTH-1:0] result,
    output logic             zero
);
    always_comb begin
        case (op)
            3'b000: result = a + b;
            3'b001: result = a - b;
            3'b010: result = a & b;
            3'b011: result = a | b;
            3'b100: result = a ^ b;
            3'b101: result = ~a;
            3'b110: result = a << 1;
            3'b111: result = a >> 1;
            default: result = '0;
        endcase
        zero = (result == '0);
    end
endmodule

module alu_tb;
    logic [7:0] a, b, result;
    logic [2:0] op;
    logic zero;

    alu dut(.a(a), .b(b), .op(op), .result(result), .zero(zero));

    initial begin
        a = 8'd10; b = 8'd5;
        op = 3'b000; #10; // add
        $display("10 + 5 = %0d (zero=%b)", result, zero);

        op = 3'b001; #10; // sub
        $display("10 - 5 = %0d", result);

        op = 3'b010; #10; // and
        $display("10 & 5 = %0d", result);

        a = 8'd0; b = 8'd0;
        op = 3'b000; #10; // add zeros
        $display("0 + 0 = %0d (zero=%b)", result, zero);

        $finish;
    end
endmodule
