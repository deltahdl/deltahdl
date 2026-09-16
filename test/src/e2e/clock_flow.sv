// §16.13.3 Clock flow: the scope of a clocking event flows left to right
// across the linear operators, concatenation, implication and the like, and
// distributes to the operands of the branching ones, and or if-else among
// them, until another replaces it; it flows into parentheses and into an
// instance of a named sequence, and out of neither, a clock named inside
// them reaching no further; and of two clocking events juxtaposed the
// second nullifies the first. clk0 rises at 5, 15, ..., 75 so that tick n
// of it is at 10n - 5, the tick counter counting through, and clk1 rises at
// 12, 27, 45, 57 and 72, reading the counter as 2, 3, 5, 6 and 8.
//
// written and implied are the clause's first pair: clk0 flows across |=>
// into the consequent, so naming it there again changes nothing, and both
// read y a tick of clk0 after x and z at the tick of clk1 after that, which
// holds from 5, at 27, and fails from 35, at 57. concat and nested are the
// clause's adjoint pair, x ##1 y |=> z and x |=> y |=> z with z on clk1,
// and read the same. paren, w ##1 (x2 ##1 @(posedge clk1) y2) |=> z2, has
// y2 on clk1 and z2 on clk0, the clock in the parentheses flowing no
// further: from 5, w, x2 at 15 and y2 at 27 match, and z2 is read at 35,
// the tick of clk0 after 27, where it holds. distribute, v |=> (w3 ##1
// @(posedge clk1) x3) and (y3 ##1 z3), has clk0 distributed to both
// operands of the and and x3 alone on clk1: from 45 the consequent begins
// at 55, x3 is read at 57 and z3 at 65, where both hold. instance, xi |=>
// s_d ##1 zi with s_d declared on clk1, reads yd at 12, the tick of clk1
// after 5, and zi at 15, the tick of clk0 after 12, the declaration's clock
// flowing no further than the instance, where both hold. juxtaposed,
// @(posedge clk1) @(posedge clk0) xj, is @(posedge clk0) xj, which holds
// at 5 and 35, where xj is high, and fails at the six other ticks of clk0.
module clock_flow;
  logic clk0 = 0;
  logic clk1 = 0;
  int tick = 1;
  logic x, y, z, w, x2, y2, z2, v, w3, x3, y3, z3, xi, yd, zi, xj;
  int written_pass = 0, written_fail = 0;
  int implied_pass = 0, implied_fail = 0;
  int concat_pass = 0, concat_fail = 0;
  int nested_pass = 0, nested_fail = 0;
  int paren_pass = 0, paren_fail = 0;
  int distribute_pass = 0, distribute_fail = 0;
  int instance_pass = 0, instance_fail = 0;
  int juxtaposed_pass = 0, juxtaposed_fail = 0;
  string written_at = "", implied_at = "", concat_at = "", nested_at = "";
  string paren_at = "", distribute_at = "", instance_at = "", juxtaposed_at = "";
  always #5 clk0 = ~clk0;
  always #10 tick = tick + 1;
  initial begin
    #12 clk1 = 1;
    #8 clk1 = 0;
    #7 clk1 = 1;
    #8 clk1 = 0;
    #10 clk1 = 1;
    #5 clk1 = 0;
    #7 clk1 = 1;
    #8 clk1 = 0;
    #7 clk1 = 1;
    #6 clk1 = 0;
  end

  assign x = tick inside {1, 4};
  assign y = tick inside {2, 5};
  assign z = tick inside {3};
  assign w = tick inside {1};
  assign x2 = tick inside {2};
  assign y2 = tick inside {3};
  assign z2 = tick inside {4};
  assign v = tick inside {5};
  assign w3 = tick inside {6};
  assign x3 = tick inside {6};
  assign y3 = tick inside {6};
  assign z3 = tick inside {7};
  assign xi = tick inside {1};
  assign yd = tick inside {2};
  assign zi = tick inside {2};
  assign xj = tick inside {1, 4};

  sequence s_d;
    @(posedge clk1) yd;
  endsequence

  written: assert property (@(posedge clk0)
                            x |=> @(posedge clk0) y ##1 @(posedge clk1) z)
    written_pass++;
    else begin
      written_fail++;
      written_at = $sformatf("%s %0d", written_at, $time);
    end

  implied: assert property (@(posedge clk0) x |=> y ##1 @(posedge clk1) z)
    implied_pass++;
    else begin
      implied_fail++;
      implied_at = $sformatf("%s %0d", implied_at, $time);
    end

  concat: assert property (@(posedge clk0) x ##1 y |=> @(posedge clk1) z)
    concat_pass++;
    else begin
      concat_fail++;
      concat_at = $sformatf("%s %0d", concat_at, $time);
    end

  nested: assert property (@(posedge clk0) x |=> y |=> @(posedge clk1) z)
    nested_pass++;
    else begin
      nested_fail++;
      nested_at = $sformatf("%s %0d", nested_at, $time);
    end

  paren: assert property (@(posedge clk0)
                          w ##1 (x2 ##1 @(posedge clk1) y2) |=> z2)
    paren_pass++;
    else begin
      paren_fail++;
      paren_at = $sformatf("%s %0d", paren_at, $time);
    end

  distribute: assert property (@(posedge clk0)
                               v |=> (w3 ##1 @(posedge clk1) x3) and (y3 ##1 z3))
    distribute_pass++;
    else begin
      distribute_fail++;
      distribute_at = $sformatf("%s %0d", distribute_at, $time);
    end

  inst_flow: assert property (@(posedge clk0) xi |=> s_d ##1 zi)
    instance_pass++;
    else begin
      instance_fail++;
      instance_at = $sformatf("%s %0d", instance_at, $time);
    end

  juxtaposed: assert property (@(posedge clk1) @(posedge clk0) xj)
    juxtaposed_pass++;
    else begin
      juxtaposed_fail++;
      juxtaposed_at = $sformatf("%s %0d", juxtaposed_at, $time);
    end

  initial begin
    #80;
    $display("x |=> @(posedge clk0) y ##1 @(posedge clk1) z passes %0d fails %0d at%s",
             written_pass, written_fail, written_at);
    $display("x |=> y ##1 @(posedge clk1) z passes %0d fails %0d at%s",
             implied_pass, implied_fail, implied_at);
    $display("x ##1 y |=> @(posedge clk1) z passes %0d fails %0d at%s",
             concat_pass, concat_fail, concat_at);
    $display("x |=> y |=> @(posedge clk1) z passes %0d fails %0d at%s",
             nested_pass, nested_fail, nested_at);
    $display("w ##1 (x2 ##1 @(posedge clk1) y2) |=> z2 passes %0d fails %0d at%s",
             paren_pass, paren_fail, paren_at);
    $display("v |=> (w3 ##1 @(posedge clk1) x3) and (y3 ##1 z3) passes %0d fails %0d at%s",
             distribute_pass, distribute_fail, distribute_at);
    $display("xi |=> s_d ##1 zi passes %0d fails %0d at%s", instance_pass,
             instance_fail, instance_at);
    $display("@(posedge clk1) @(posedge clk0) xj passes %0d fails %0d at%s",
             juxtaposed_pass, juxtaposed_fail, juxtaposed_at);
    $finish;
  end
endmodule
