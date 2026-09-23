/*
:subclause: 8.25
:stage: simulation
*/
class S #(type T = int);
  static int n = 0;
  function new();
    n++;
  endfunction
endclass

module top;
  initial begin
    automatic S s = new;
    automatic S #(byte) b1 = new;
    automatic S #(byte) b2 = new;
    $display(":assert: (%0d == 1)", s.n);
    $display(":assert: (%0d == 2)", S#(byte)::n);
    $display(":assert: (%0d == 0)", S#(shortint)::n);
  end
endmodule
