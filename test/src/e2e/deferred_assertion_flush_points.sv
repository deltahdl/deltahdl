module deferred_assertion_flush_points;
  task automatic note(input string what);
    $display("%s", what);
  endtask

  logic a = 0;
  logic not_a = 1;
  always_comb begin : b1
    a1: assert (not_a != a) else note("a1: reported the glitch, not_a still equal to a");
    a2: assert #0 (not_a != a) else note("a2: never reported");
  end

  logic x = 0;
  logic y = 0;
  always @(x or y) begin : b2
    a3: assert #0 (x == y) note("a3: pass"); else note("a3: fail");
    #1;
    a4: assert #0 (x == y) note("a4: pass"); else note("a4: fail");
  end

  int p = 0;
  int q = 0;
  always_comb begin : b3
    c1: cover (q != p) note("c1: covered while q lagged p");
    c2: cover #0 (q != p) note("c2: never reported");
  end

  bit s = 0;
  bit t = 0;
  bit u;
  function void say(input string what);
    $display("%s", what);
  endfunction
  function bit f(input bit v);
    $display("f called with %0d", v);
    pf: assert #0 (v) say("pf: pass"); else say("pf: fail");
    return v;
  endfunction
  always_comb begin : myblk
    u = t || f(s);
  end

  bit my_cond = 1;
  int opcode = 0;
  int seen;
  function int error_type(input int op);
    func_assert: assert (op < 64) else $display("Opcode error.");
    if (op < 32) return 0;
    else return 1;
  endfunction
  always_comb begin : b4
    seen = opcode;
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
    #10 opcode = 64;
    my_cond = 0;
    #0 opcode = 0;
    #1 $finish;
  end
endmodule
