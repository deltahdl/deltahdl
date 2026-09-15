// §16.4.4 Disabling deferred assertions: a disable naming a specific deferred
// assertion cancels that assertion's pending reports; a disable applied to the
// outermost scope of a procedure with an active deferred assertion queue
// flushes the queue, every pending report on it cleared, beside the ordinary
// effects of §9.6.2; and a disable of a task or of a scope that is not a
// procedure's outermost one flushes nothing. The clause's two examples are run
// with $error standing where its first has $fatal, so that the run goes on.
module disable_deferred_assertions;
  // The first example: a1's failure is reported only in a time step where
  // bad_val_ok does not settle at 1, the disable a1 cancelling it otherwise.
  logic bad_val = 0;
  logic bad_val_ok = 0;
  always @(bad_val or bad_val_ok) begin : b1
    a1: assert #0 (bad_val) else $error("Sorry");
    if (bad_val_ok) begin
      disable a1;
    end
  end

  // The second example: a disable of b2 from b3 flushes every report pending
  // on b2's queue.
  logic a = 0;
  logic b = 0;
  logic [7:0] c = 0;
  logic clear_b2 = 0;
  always @(a or b or c) begin : b2
    if (c == 8'hff) begin
      a2: assert #0 (a && b) else $error("a2: a and b are not both 1");
    end else begin
      a3: assert #0 (a || b) else $error("a3: neither a nor b is 1");
    end
  end
  always @(clear_b2) begin : b3
    disable b2;
  end

  // A disable of a scope that is not the procedure's outermost one leaves the
  // report a4 queued in it pending, and it is reported.
  logic d = 1;
  always @(d) begin : b4
    begin : inner
      a4: assert #0 (d) else $error("a4: d is 0");
      disable inner;
    end
  end

  // A disable of a task leaves the report its call queued pending as well.
  logic e = 1;
  task t_check;
    a5: assert #0 (e) else $error("a5: e is 0");
  endtask
  always @(e) begin : b5
    t_check();
    disable t_check;
  end

  initial begin
    #10 bad_val_ok = 1;
    $display("at 10: bad_val is 0 and bad_val_ok settles at 1, so a1's failure is cancelled");
    #10 bad_val_ok = 0;
    $display("at 20: bad_val_ok settles at 0, so a1's failure is reported");
    #10 bad_val = 1;
    $display("at 30: bad_val is 1, so a1 passes");
    #10 c = 8'hff;
    $display("at 40: c is ff with a and b at 0, so a2's failure is reported");
    #10 c = 0;
    #0 clear_b2 = 1;
    $display("at 50: a3 failed, then b3 disabled b2 and flushed its queue");
    #10 c = 8'hff;
    $display("at 60: c is ff again, so a2's failure is reported");
    #10 d = 0;
    $display("at 70: d is 0, and the disable of inner leaves a4 reported");
    #10 e = 0;
    $display("at 80: e is 0, and the disable of t_check leaves a5 reported");
    #10 $finish;
  end
endmodule
