module gate_array;
  logic [3:0] a, b;
  wire [3:0] y;

  // §28.3.6 Example 2 states that an array of gate instances and the separate
  // declarations `and g3 (y[3], a[3], b[3]);` and so on are "equivalent except
  // for indexed instance names", so each element answers a later change of its
  // own input bit. udp_array.sv is the same claim over a user-defined
  // primitive; no other source here instantiates a gate array at all.
  and ga [3:0] (y, a, b);

  initial begin
    a = 4'b1100;
    b = 4'b1010;
    #1 $display("a=%b b=%b y=%b", a, b, y);
    b = 4'b0101;
    #1 $display("a=%b b=%b y=%b", a, b, y);
  end
endmodule
