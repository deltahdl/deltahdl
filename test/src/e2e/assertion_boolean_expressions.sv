module assertion_boolean_expressions;
  logic clk = 0;
  logic [2:0] v;
  int q[$];
  int q_held = 0;
  always #5 clk = ~clk;

  bool_v: assert property (@(posedge clk) v)
    $display("v sampled %b at %0d is true", v, $time);
  else
    $display("v sampled %b at %0d is false", v, $time);

  q_head: assert property (@(posedge clk) q[0] == 5)
    q_held = q_held + 1;

  initial begin
    q.push_back(5);
    #7 v = 3'bzzz;
    #8 q.pop_front();
    #2 v = 3'b000;
    #10 v = 3'b010;
    #10 v = 3'b100;
    #20;
    $display("q[0] == 5 held at %0d of 6 ticks, the tick in whose time step q was emptied among them", q_held);
    $finish;
  end
endmodule
