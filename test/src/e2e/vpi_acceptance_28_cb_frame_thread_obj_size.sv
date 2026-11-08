`timescale 1ns/1ns
module top;
  class C; endclass
  C c;
  int q[$];
  task automatic t(); #0; endtask
  initial begin
    #1 q.push_back(7); q.push_back(8);
    #1 void'(q.pop_front());
    t(); t();
    fork #1; #1; join
    c = new; c = new; c = new;
  end
endmodule
