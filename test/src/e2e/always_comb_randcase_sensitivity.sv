// IEEE 1800-2023 9.2.2.2.1: the implicit sensitivity list of an always_comb
// holds every net or variable read within the block, and its three exceptions
// name a declaration, a write and a timing control expression -- never a
// statement position. A randcase item is a statement within the block, so the
// read of `a` inside it belongs to the list and moving `a` re-evaluates the
// procedure.
//
// The unconditional `y = 8'd99;` gives the block an output on every path, so a
// run in which the randcase item never executed would print 99 rather than a
// stale earlier value. The single item's weight of 3 is non-zero, so 18.16
// selects it on every draw.
module always_comb_randcase_sensitivity;
  logic [7:0] a = 8'd10;
  logic [7:0] y;

  always_comb begin
    y = 8'd99;
    randcase
      3 : y = a + 8'd3;
    endcase
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
