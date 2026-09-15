// §16.4.3 Deferred assertions outside procedural code: a deferred assertion
// written as a module item, a static deferred assertion, is treated as if it
// were the one statement of an always_comb procedure. It is therefore
// evaluated once at time zero and again whenever an operand of its expression
// changes, its reports mature in the Reactive or Postponed region of the time
// step that evaluated them, and a re-run within that time step flushes the
// reports the superseded evaluation queued, as §16.4.2 has for any always_comb.
module m (input logic [3:0] a, input logic [3:0] b);
  a1: assert #0 (a == b) else $error("a1: a is %0d and b is %0d", a, b);
  f1: assert final (a == b) else $error("f1: a is %0d and b is %0d", a, b);
  c1: cover #0 (a != b) $display("c1: covered a %0d against b %0d", a, b);
endmodule

module static_deferred_assertions;
  logic [3:0] a = 0;
  logic [3:0] b = 0;
  m u (.a(a), .b(b));

  initial begin
    // At time zero the three are evaluated once with a and b equal: the
    // assertions pass and the cover is evaluated without succeeding.
    #10 a = 5;
    // At 10 both assertions fail, a1 reporting in the Reactive region and f1
    // in the Postponed region, and the cover succeeds.
    #10 b = 5;
    // At 20 a and b are equal again: the assertions pass, the cover does not.
    #10 a = 7;
    #0 b = 7;
    // At 30 the evaluation that saw a at 7 against b at 5 queued two failures
    // and a success, which the re-run for b's write flushed: nothing of that
    // evaluation is reported or counted, and the re-run finds the two equal.
    #10 $finish;
  end
endmodule
