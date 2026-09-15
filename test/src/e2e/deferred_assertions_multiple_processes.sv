// §16.4.5 Deferred assertions and multiple processes: a deferred assertion is
// associated with the process executing it, so one written in a function is
// executed once per process that calls the function, and each process's
// execution is independent. This is the clause's example, the function f with
// its assertion a1 called from the two always_comb procedures b1 and b2, driven
// through the clause's three time steps.
module deferred_assertions_multiple_processes;
  int x = 0;
  int y = 0;
  int z = 0;
  int w = 0;
  bit some_stuff;
  bit other_stuff;

  function bit f(input int a, input int b);
    a1: assert #0 (a == b) else $error("a1: a is %0d and b is %0d", a, b);
    return a == b;
  endfunction

  always_comb begin : b1
    some_stuff = f(x, y) ? 1 : 0;
  end

  always_comb begin : b2
    other_stuff = f(z, w) ? 1 : 0;
  end

  initial begin
    // Time step 1: b1 executes with x != y and b2 with z != w, so a1 fails
    // independently in each process and its failure is reported twice.
    #10 x = 1;
    z = 1;
    $display("at 10: a1 fails in b1 and in b2, and is reported twice");
    // Time step 2: b1 executes with x != y, then again with x == y, so the
    // first failure is flushed and the final execution passes.
    #10 x = 2;
    #0 y = 2;
    $display("at 20: b1's first failure is flushed by its re-run, which passes");
    // Time step 3: b1 executes with x != y and sees no flush point, so that
    // failure is reported; b2 executes with z == w and passes.
    #10 x = 3;
    w = 1;
    $display("at 30: a1 fails in b1 alone, and b2 passes");
    #10 $finish;
  end
endmodule
