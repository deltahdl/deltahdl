// §16.14.7 Inferred clocking and disable functions: $inferred_clock and
// $inferred_disable, used as the entire default value of a formal argument
// of a property, are replaced at the point the property is instantiated by
// the clocking event and the disable condition inferred there: for an
// instance that is the top-level property expression of an assertion
// statement, the event expression determined at the statement's location,
// the default clocking of the scope for a static assertion and the clock
// inferred from the procedure for a procedural one, and the condition of
// the default disable iff whose scope includes the call, 1'b0 outside any;
// an actual argument supplied for the formal stands instead. The clause's
// p_triggers is instantiated by its a1, a2 and a3 beside the assertion
// each is logically equivalent to, and each pair reports alike: a1 and
// a1_explicit on negedge clk1 disabled while rst1, a2 and a2_explicit on
// posedge clk1 disabled by 1'b0, and a3 and a3_explicit, in the always
// procedure, on posedge clk2 disabled while rst1. clk1 rises at 5, 15, ...
// and falls at 10, 20, ..., clk2 rises at 13 and 33, a and b are 1
// throughout, so each attempt's antecedent matches at its own tick and
// its consequent reads c at the next, c is 1 from 12 to 28, rst1 is 1
// from 36 to 42, disabling a1's attempt of 40 and dropping its attempt of
// 30, and the run ends at 48, where the attempts still in flight hold.
module inferred_clocking_functions;
  logic a = 1, b = 1, c = 0, d = 0, rst1 = 0, clk1 = 0, clk2 = 0;
  logic rst = 0;
  int rst_seen = 0;
  always #5 clk1 = ~clk1;
  initial begin
    #3;
    forever #10 clk2 = ~clk2;
  end

  default clocking @(negedge clk1); endclocking
  default disable iff rst1;

  property p_triggers(start_event, end_event, form, clk = $inferred_clock,
                      rst = $inferred_disable);
    @clk disable iff (rst) (start_event ##0 end_event[->1]) |=> form;
  endproperty

  a1: assert property (p_triggers(a, b, c))
    $display("a1 passed at %0d", $time);
  else $display("a1 failed at %0d", $time);
  a1_explicit: assert property (@(negedge clk1) disable iff (rst1)
                                (a ##0 b[->1]) |=> c)
    $display("a1_explicit passed at %0d", $time);
  else $display("a1_explicit failed at %0d", $time);

  a2: assert property (p_triggers(a, b, c, posedge clk1, 1'b0))
    $display("a2 passed at %0d", $time);
  else $display("a2 failed at %0d", $time);
  a2_explicit: assert property (@(posedge clk1) disable iff (1'b0)
                                (a ##0 b[->1]) |=> c)
    $display("a2_explicit passed at %0d", $time);
  else $display("a2_explicit failed at %0d", $time);

  always @(posedge clk2 or posedge rst) begin
    if (rst) rst_seen++;
    else begin
      a3: assert property (p_triggers(a, b, c))
        $display("a3 passed at %0d", $time);
      else $display("a3 failed at %0d", $time);
      a3_explicit: assert property (@(posedge clk2) disable iff (rst1)
                                    (a ##0 b[->1]) |=> c)
        $display("a3_explicit passed at %0d", $time);
      else $display("a3_explicit failed at %0d", $time);
    end
  end

  initial begin
    #12 c = 1;
    #16 c = 0;
    #8 rst1 = 1;
    #6 rst1 = 0;
    #6 $finish;
  end
endmodule
