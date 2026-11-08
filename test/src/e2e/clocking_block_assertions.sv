module A(input logic clk, input logic a);
  clocking cb_with_input @(posedge clk);
    input a;
    property p1;
      a;
    endproperty
  endclocking

  clocking cb_without_input @(posedge clk);
    property p1;
      a;
    endproperty
  endclocking

  property p1;
    @(posedge clk) a;
  endproperty

  property p2;
    @(posedge clk) cb_with_input.a;
  endproperty

  a1: assert property (p1) $display("a1 passed at %0d", $time); else;
  a2: assert property (cb_with_input.p1)
    $display("a2 passed at %0d", $time); else;
  a3: assert property (p2) $display("a3 passed at %0d", $time); else;
  a4: assert property (cb_without_input.p1)
    $display("a4 passed at %0d", $time); else;
endmodule

module clocking_block_assertions;
  logic clk = 0;
  logic a = 0;
  always #5 clk = ~clk;
  A u1(clk, a);
  initial begin
    #20 a = 1;
    #20 a = 0;
    #20 $finish;
  end
endmodule
