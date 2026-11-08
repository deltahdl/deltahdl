module contassign_delay;
  logic [7:0] a;
  logic [7:0] b;
  wire [7:0] y;

  assign #6 y = a & b;

  initial begin
    a = 8'hF0;
    b = 8'hCC;
    #9;
    a = 8'h3C;
    b = 8'h7A;

    #2;
    $display("held y=%h", y);
    #7;
    $display("propagated y=%h", y);
  end
endmodule
