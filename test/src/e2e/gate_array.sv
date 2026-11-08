module gate_array;
  logic [3:0] a, b;
  wire [3:0] y;

  and ga [3:0] (y, a, b);

  initial begin
    a = 4'b1100;
    b = 4'b1010;
    #1 $display("a=%b b=%b y=%b", a, b, y);
    b = 4'b0101;
    #1 $display("a=%b b=%b y=%b", a, b, y);
  end
endmodule
