// §16.4.2 Deferred assertion flush points: a process reaches one when it
// resumes after suspending on an event control or a wait statement, when it is
// an always_comb or always_latch resumed by a transition on a dependent signal,
// or when its outermost scope is disabled. Each of the clause's examples is run
// here with the arbitrary ordering the clause describes made definite by a #0:
// the second write of a time step comes from the Inactive region, so the
// procedure sees the transitional values once and the settled values after.
module deferred_assertion_flush_points;
  task automatic note(input string what);
    $display("%s", what);
  endtask

  // The clause's first example: a simple immediate assertion may report the
  // moment not_a has not yet followed a, and the deferred one does not, its
  // report being flushed when the procedure re-runs on not_a's change.
  logic a = 0;
  logic not_a = 1;
  always_comb begin : b1
    a1: assert (not_a != a) else note("a1: reported the glitch, not_a still equal to a");
    a2: assert #0 (not_a != a) else note("a2: never reported");
  end

  // The time-delay example: a3's report always matures, an Observed region
  // coming before any flush point; a4's failure at 21 is flushed when y changes
  // after it in that time step and the procedure resumes at its event control.
  logic x = 0;
  logic y = 0;
  always @(x or y) begin : b2
    a3: assert #0 (x == y) note("a3: pass"); else note("a3: fail");
    #1;
    a4: assert #0 (x == y) note("a4: pass"); else note("a4: fail");
  end

  // The cover example: the simple cover is credited by q lagging p, the
  // deferred one is not, so only c1 shows a success at the end of simulation.
  int p = 0;
  int q = 0;
  always_comb begin : b3
    c1: cover (q != p) note("c1: covered while q lagged p");
    c2: cover #0 (q != p) note("c2: never reported");
  end

  // The short-circuiting example: f runs while t is 0 and its assertion passes
  // with s at 1, then t becomes 1 and s 0 in the same step; the resumed
  // procedure short-circuits past f, so pf's failing value is never seen and
  // the Reactive region reports nothing for it.
  bit s = 0;
  bit t = 0;
  bit u;
  function bit f(input bit v);
    $display("f called with %0d", v);
    pf: assert #0 (v) note("pf: pass"); else note("pf: fail");
    return v;
  endfunction
  always_comb begin : myblk
    u = t || f(s);
  end

  // The argument evaluation example: the action block's arguments are
  // evaluated on every failure, so error_type runs with 64 on the first pass
  // and its own assertion prints, though that pass's reports are flushed; the
  // reports that mature carry the 0 of the second pass.
  bit my_cond = 1;
  int opcode = 0;
  function int error_type(input int op);
    func_assert: assert (op < 64) else $display("Opcode error.");
    if (op < 32) return 0;
    else return 1;
  endfunction
  always_comb begin : b4
    e1: assert #0 (my_cond) else $error("Error on operation of type %0d", error_type(opcode));
    e2: assert #0 (my_cond) else void'(error_type(opcode));
  end

  initial begin
    #10 a = 1;
    #0 not_a = 0;
    #10 x = 1;
    #1;
    #0 y = 1;
    #9 p = 7;
    #0 q = 7;
    #10 s = 1;
    #0 begin
      t = 1;
      s = 0;
    end
    #10 my_cond = 0;
    opcode = 64;
    #0 opcode = 0;
    #1 $finish;
  end
endmodule
