// IEEE 1800-2023 16.1 (printed page 383) lists what clause 16 describes:
// immediate assertions, concurrent assertions, sequence specifications and
// property specifications. This design holds one of each, and its output is
// what the subclauses defining them specify.
//
// The concurrent assertion is an instance of the named property (16.12.1) on
// every posedge of clk (16.14.5 gives an assertion outside procedural code
// always semantics). Edges fall at 5, 15, 25, 35 and 45, and the stimulus
// changes between them, so each tick sees one value of req and en whatever
// region samples it. The property holds at four ticks and fails at the one
// where req is high with en low, so 16.14.1 runs the pass statement four
// times and the fail statement once, at time 35.
//
// The named sequence is req followed one cycle later by ack. ack is req
// delayed one clock by the always_ff, so req high at the 15 tick gives ack
// high at the 25 tick and the sequence reaches its end point there. 16.13.6
// has triggered true at the point in time where the sequence's end point is
// reached and usable in a wait statement, so the waiting process wakes at 25.
//
// The two immediate assertions at the end test the counts as 16.3 has an
// immediate assertion test its expression when the statement executes: the
// first holds and takes its pass statement, the second does not and takes its
// fail statement. Both branches printing is what shows the assertion was
// evaluated rather than skipped.
module assertions_general;
  logic clk = 1'b0;
  logic en = 1'b1;
  logic req = 1'b0;
  logic ack = 1'b0;
  int passes = 0;
  int fails = 0;

  always #5 clk = ~clk;

  always_ff @(posedge clk) ack <= req;

  sequence req_then_ack;
    @(posedge clk) req ##1 ack;
  endsequence

  property req_only_when_enabled;
    @(posedge clk) !req || en;
  endproperty

  assert property (req_only_when_enabled)
    passes = passes + 1;
  else begin
    fails = fails + 1;
    $display("concurrent: req while disabled at %0d", $time);
  end

  initial begin
    wait (req_then_ack.triggered);
    $display("sequence: req then ack matched at %0d", $time);
  end

  initial begin
    #10 req = 1'b1;
    #10 req = 1'b0;
    #10 en = 1'b0;
    req = 1'b1;
    #10 req = 1'b0;
    #6;
    assert (passes == 4) $display("immediate: %0d ticks held", passes);
    else $display("immediate: %0d ticks held, expected 4", passes);
    assert (fails == 0) $display("immediate: no tick failed");
    else $display("immediate: %0d tick failed", fails);
    $finish;
  end
endmodule
