module property_instantiation_operand;
  logic clk, rst, a, b;
  property leaf;
    @(posedge clk) disable iff (rst) a |-> b;
  endproperty
  property outer;
    @(posedge clk) not leaf();
  endproperty
endmodule
