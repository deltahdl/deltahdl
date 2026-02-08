module counter #(parameter WIDTH = 8)(
    input logic clk,
    input logic rst,
    output logic [WIDTH-1:0] count
);
    always_ff @(posedge clk or posedge rst)
        if (rst) count <= '0;
        else count <= count + 1;
endmodule

module counter_tb;
    logic clk = 0;
    logic rst;
    logic [7:0] count;

    counter dut(.clk(clk), .rst(rst), .count(count));

    initial begin
        rst = 1;
        #10 rst = 0;
        #100 $finish;
    end

    always #5 clk = ~clk;
endmodule
