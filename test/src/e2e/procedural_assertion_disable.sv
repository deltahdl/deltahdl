// §16.14.6.4 Disabling procedural concurrent assertions: a disable naming a
// specific procedural concurrent assertion clears the pending instances of
// that assertion from the procedural assertion queue and leaves those of
// the other assertions where they are; a disable applied to the outermost
// scope of a procedure with a pending procedural assertion queue flushes
// the queue, every pending instance cleared, beside the activities of
// §9.6.2; and an evaluation attempt that has matured is impacted by no
// disable. clk rises at 5, 15, ..., 45 and is the default clocking, a and
// b are 1 throughout, so every attempt passes, and the run ends at 50.
//
// b1 queues a1 and a2 at each change of go. At 10 it delays before
// disabling a1, so the two instances mature in the Observed region first
// and a1 and a2 pass at 15. At 20 it disables a1 in the same time step,
// so a1's pending instance is cleared where a2's stays, and a2 alone
// passes at 25. b2 queues a3 and a4 at each change of go2, and b3
// disables b2, b2's outermost scope, at each change of clear_b2: at 30
// both change at once, go2 first, so b3 flushes what b2 queued in the
// same step and nothing passes at 35; at 40 go2 changes alone, the
// instances mature, and the disable of 41 reaches them no more, so a3 and
// a4 pass at 45.
module procedural_assertion_disable;
  logic clk = 0;
  logic a = 1, b = 1;
  int go = 0, go2 = 0;
  logic clear_b2 = 0;
  always #5 clk = ~clk;

  default clocking @(posedge clk); endclocking

  always @(go) begin : b1
    a1: assert property (const'(a)) $display("a1 passed at %0d", $time);
    else $display("a1 failed at %0d", $time);
    a2: assert property (const'(b)) $display("a2 passed at %0d", $time);
    else $display("a2 failed at %0d", $time);
    if (go == 2) disable a1;
    else begin
      #1 disable a1;
    end
  end

  always @(go2) begin : b2
    a3: assert property (const'(a)) $display("a3 passed at %0d", $time);
    else $display("a3 failed at %0d", $time);
    a4: assert property (const'(b)) $display("a4 passed at %0d", $time);
    else $display("a4 failed at %0d", $time);
  end

  always @(clear_b2) begin : b3
    disable b2;
  end

  initial begin
    #10 go = 1;
    #10 go = 2;
    #10 go2 = 1;
    clear_b2 = 1;
    #10 go2 = 2;
    #1 clear_b2 = 0;
    #9 $finish;
  end
endmodule
