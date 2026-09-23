/*
:subclause: 8.25
:stage: simulation
*/
typedef int iq_t[$];

class S #(type T = int);
  T value;
endclass

module top;
  initial begin
    automatic S #(iq_t) s = new;
    s.value.push_back(4);
    s.value.push_back(9);
    $display(":assert: (%0d == 2)", s.value.size());
    $display(":assert: (%0d == 9)", s.value[1]);
  end
endmodule
