/*
:subclause: 8.25
:stage: simulation
*/
typedef int word_t;

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
    automatic S #(word_t) w = new;
    $display(":assert: (%0d == 3)", S#(int)::n);
    $display(":assert: (%0d == 3)", s.n);
  end
endmodule
