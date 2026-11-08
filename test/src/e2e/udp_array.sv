primitive udp_and2 (y, a, b);
  output y;
  input a, b;
  table
       0 0 : 0 ;
       0 1 : 0 ;
       1 0 : 0 ;
       1 1 : 1 ;
  endtable
endprimitive

module udp_array;
  logic [3:0] a;
  logic [3:0] b;
  logic enable;
  wire [3:0] y;
  wire [3:0] z;

  udp_and2 ga [3:0] (y, a, b);
  udp_and2 gb [3:0] (z, a, enable);

  initial begin
    a = 4'b1100;
    b = 4'b1010;
    enable = 1;
    #1;
    $display("a=1100 b=1010 y=%b", y);
    $display("a=1100 enable=1 z=%b", z);

    b = 4'b0101;
    enable = 0;
    #1;
    $display("a=1100 b=0101 y=%b", y);
    $display("a=1100 enable=0 z=%b", z);
  end
endmodule
