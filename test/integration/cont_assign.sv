module cont_assign;
  logic [7:0] a;
  logic [7:0] b;
  logic [7:0] sum;

  assign sum = a + b;

  initial begin
    a = 10;
    b = 20;
    #1;
    $display("%d", sum);
  end
endmodule
