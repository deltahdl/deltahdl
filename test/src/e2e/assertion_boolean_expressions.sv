// §16.6 Boolean expressions: the value of an assertion's expression is read as
// the condition of an if statement is, false for x, z and 0 and true for any
// other value, and the expression is evaluated over the sampled values of its
// variables, an element of a queue sampled for the evaluation continuing to
// exist for it though the queue is emptied before the evaluation runs. v takes
// x, z, 0, 2 and 4 between the ticks at 5, 15, 25, 35, 45 and 55; q holds 5
// from time zero and is emptied in the time step of the tick at 15.
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
