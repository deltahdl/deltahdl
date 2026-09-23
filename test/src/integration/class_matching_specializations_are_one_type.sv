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
    automatic S #(int) i = new;
    $display(":assert: (%0d == 2)", S#(int)::n);
    $display(":assert: (%0d == 2)", s.n);
  end
endmodule
