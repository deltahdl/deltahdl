// §16.12.1 Property instantiation: an instance of a named property used as
// the operand of a property-building operator must, its body substituted,
// yield a legal property_expr, and a body carrying a disable iff clause is a
// property_spec rather than a property_expr, so such a property may not be
// instantiated as an operand. leaf carries a disable iff clause and outer
// instantiates it as the operand of not, which is reported.
module property_instantiation_operand;
  logic clk, rst, a, b;
  property leaf;
    @(posedge clk) disable iff (rst) a |-> b;
  endproperty
  property outer;
    @(posedge clk) not leaf();
  endproperty
endmodule
