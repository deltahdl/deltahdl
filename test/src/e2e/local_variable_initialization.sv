// §16.13.7 Local variable initialization assignments: for a singly clocked
// property, the initialization assignment of a local variable is performed
// when the evaluation attempt of the instance begins, at a tick of its one
// clock; for a multiclock property with a single semantic leading clock,
// at the earliest tick of that clock at or after the attempt begins; and
// where an instance has two or more semantic leading clocks, a separate
// copy of the local is created for each, initialized at the earliest tick
// of its clock at or after the attempt begins and read by the subproperty
// on that clock. clk rises at 5, 15, 25, ..., clk1 at 18, 38, 58, ... and
// clk2 at 22, 42, 62, .... f is high at 5 alone, so each assertion's
// attempt at 5 is the one that is not vacuous; the other nine, at 15 to
// 95, pass vacuously. e is 1 before 10 and from 16 to 20, so it is 1 at 5
// and at 18 and 0 at 15 and at 22.
//
// p is the clause's property: its instance begins at 15, after f, and its
// two subproperties are on clk1 and clk2, so v is copied twice, the clk1
// copy initialized at 18, to 1, and the clk2 copy at 22, to 0. a is 1 at
// 18 alone and b is 1 there, so (a == v)[*1:$] matches at 18 and b holds;
// c is 1 at 22 alone and d is 0, so c[*1:$] matches at 22 and d == v
// holds: p passes. p with d != v reads the clk2 copy the other way and
// fails at 22, which shows that copy is 0 and not the 1 that e held at 18
// or at 5. r has clk1 alone as its semantic leading clock, so u is
// initialized at 18, to 1, and (a == u)[*1:$] matches at 18 with b
// holding; r with !b as its consequent fails at 18, where the match is,
// which shows u is 1 and not the 0 that e held at 15, where the attempt
// began, since a == 0 does not hold at 18. q is singly clocked, on the clock flowing in from the assertion,
// so w is initialized at 5, where the attempt begins, to 1, and g == w
// holds at 15, where g is 1; q with g != w fails at 15, which shows w is 1
// and not the 0 that e held at 15.
module local_variable_initialization;
  logic clk = 0;
  logic clk1 = 0;
  logic clk2 = 0;
  logic f = 1, e = 1, a = 0, b = 0, c = 0, d = 0, g = 0;
  int p_pass = 0, p_fail = 0, p_ne_pass = 0, p_ne_fail = 0;
  int r_pass = 0, r_fail = 0, r_ne_pass = 0, r_ne_fail = 0;
  int q_pass = 0, q_fail = 0, q_ne_pass = 0, q_ne_fail = 0;
  string p_ne_at = "", r_ne_at = "", q_ne_at = "";
  always #5 clk = ~clk;
  initial begin
    #18;
    forever begin
      clk1 = 1;
      #10 clk1 = 0;
      #10;
    end
  end
  initial begin
    #22;
    forever begin
      clk2 = 1;
      #10 clk2 = 0;
      #10;
    end
  end

  property p;
    logic v = e;
    (@(posedge clk1) (a == v)[*1:$] |-> b)
    and
    (@(posedge clk2) c[*1:$] |-> d == v);
  endproperty
  a1: assert property (@(posedge clk) f |=> p) p_pass++; else p_fail++;

  property p_ne;
    logic v = e;
    (@(posedge clk1) (a == v)[*1:$] |-> b)
    and
    (@(posedge clk2) c[*1:$] |-> d != v);
  endproperty
  a2: assert property (@(posedge clk) f |=> p_ne) p_ne_pass++;
    else begin
      p_ne_fail++;
      p_ne_at = $sformatf("%s %0d", p_ne_at, $time);
    end

  property r;
    logic u = e;
    @(posedge clk1) (a == u)[*1:$] |-> b;
  endproperty
  a3: assert property (@(posedge clk) f |=> r) r_pass++; else r_fail++;

  property r_ne;
    logic u = e;
    @(posedge clk1) (a == u)[*1:$] |-> !b;
  endproperty
  a4: assert property (@(posedge clk) f |=> r_ne) r_ne_pass++;
    else begin
      r_ne_fail++;
      r_ne_at = $sformatf("%s %0d", r_ne_at, $time);
    end

  property q;
    logic w = e;
    1'b1 ##1 (g == w);
  endproperty
  a5: assert property (@(posedge clk) f |-> q) q_pass++; else q_fail++;

  property q_ne;
    logic w = e;
    1'b1 ##1 (g != w);
  endproperty
  a6: assert property (@(posedge clk) f |-> q_ne) q_ne_pass++;
    else begin
      q_ne_fail++;
      q_ne_at = $sformatf("%s %0d", q_ne_at, $time);
    end

  initial begin
    #10 f = 0; e = 0; g = 1;
    #6 e = 1; a = 1; b = 1;
    #4 e = 0; a = 0; b = 0; g = 0; c = 1;
    #4 c = 0;
    #76;
    $display("p passes %0d fails %0d", p_pass, p_fail);
    $display("p with d != v passes %0d fails %0d at%s", p_ne_pass, p_ne_fail,
             p_ne_at);
    $display("r passes %0d fails %0d", r_pass, r_fail);
    $display("r with !b passes %0d fails %0d at%s", r_ne_pass, r_ne_fail,
             r_ne_at);
    $display("q passes %0d fails %0d", q_pass, q_fail);
    $display("q with g != w passes %0d fails %0d at%s", q_ne_pass, q_ne_fail,
             q_ne_at);
    $finish;
  end
endmodule
