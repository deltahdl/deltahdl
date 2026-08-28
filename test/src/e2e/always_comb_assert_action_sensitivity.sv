// IEEE 1800-2023 9.2.2.2.1 (printed page 223): "An expression used in an
// immediate assertion (see 16.3) within the procedure, or in any function
// called within the procedure, contributes to the implicit sensitivity list of
// an always_comb as if that expression were used as a condition of an if
// statement. Expressions used in assertion action blocks do not contribute to
// the implicit sensitivity list of an always_comb."
//
// So `en`, the assertion expression, is in the list, and `a`, read only in the
// pass statement, is not. Driving `a` from 10 to 20 leaves the procedure
// unevaluated and `y` holding the 13 that time zero produced.
//
// The unconditional `y = 8'd99;` gives the block an output on every path, so a
// run in which the pass statement never executed would print 99 rather than a
// value that happens to match.
module always_comb_assert_action_sensitivity;
  logic en = 1'b1;
  logic [7:0] a = 8'd10;
  logic [7:0] y;

  always_comb begin
    y = 8'd99;
    assert (en) y = a + 8'd3;
  end

  initial begin
    #10;
    $display("y after a = 10 is %0d", y);
    a = 8'd20;
    #10;
    $display("y after a = 20 is %0d", y);
    $finish;
  end
endmodule
