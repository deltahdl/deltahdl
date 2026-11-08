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
