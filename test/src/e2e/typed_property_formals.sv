module typed_property_formals;
  logic clk = 0;
  int tick = 1;
  logic [7:0] v;
  logic w, go, b, c;
  int untyped_pass = 0, untyped_fail = 0;
  int typed_pass = 0, typed_fail = 0;
  int ev_pass = 0, ev_fail = 0;
  int sig_pass = 0, sig_fail = 0;
  int bool_pass = 0, bool_fail = 0;
  int seq_pass = 0, seq_fail = 0;
  int prop_pass = 0, prop_fail = 0;
  int not_pass = 0, not_fail = 0;
  int ante_pass = 0, ante_fail = 0;
  always #5 clk = ~clk;
  always #10 tick = tick + 1;

  assign v = (tick inside {2, 4}) ? 8'h02 : (tick inside {6}) ? 8'h01 : 8'h00;
  assign w = tick inside {2, 6};
  assign go = tick inside {1, 3, 5, 7};
  assign b = tick inside {2, 3, 6, 7, 8};
  assign c = tick inside {2, 4};

  property p_untyped(x, y);
    @(posedge clk) x |-> y;
  endproperty

  property p_bit(bit x, y);
    @(posedge clk) x |-> y;
  endproperty

  property p_ev(event ev);
    @(ev) v == 2 |-> w;
  endproperty

  property p_sig(sig);
    @(posedge sig) v == 2 |-> w;
  endproperty

  property p_prop(property q);
    @(posedge clk) go |-> q;
  endproperty

  property p_not(property q);
    @(posedge clk) not q;
  endproperty

  property p_seq(sequence s);
    @(posedge clk) s |-> c;
  endproperty

  whole: assert property (p_untyped(v, w))
    untyped_pass++; else untyped_fail++;

  typed: assert property (p_bit(v, w))
    typed_pass++; else typed_fail++;

  ev: assert property (p_ev(posedge clk))
    ev_pass++; else ev_fail++;

  sig: assert property (p_sig(clk))
    sig_pass++; else sig_fail++;

  prop_bool: assert property (@(posedge clk) p_prop(b))
    bool_pass++; else bool_fail++;

  prop_seq: assert property (@(posedge clk) p_prop(b ##1 c))
    seq_pass++; else seq_fail++;

  prop_prop: assert property (@(posedge clk) p_prop(b or nexttime c))
    prop_pass++; else prop_fail++;

  negated: assert property (p_not(b |-> c))
    not_pass++; else not_fail++;

  seq_ante: assert property (p_seq(go ##1 b))
    ante_pass++; else ante_fail++;

  initial begin
    #80;
    $display("p_untyped(v, w), x untyped, passes %0d fails %0d at ticks",
             untyped_pass, untyped_fail);
    $display("p_bit(v, w), x a bit, passes %0d fails %0d at ticks",
             typed_pass, typed_fail);
    $display("p_ev(posedge clk) passes %0d fails %0d at ticks", ev_pass,
             ev_fail);
    $display("p_sig(clk) passes %0d fails %0d at ticks", sig_pass, sig_fail);
    $display("p_prop(b), a boolean, passes %0d fails %0d at ticks", bool_pass,
             bool_fail);
    $display("p_prop(b ##1 c), a sequence, passes %0d fails %0d at ticks",
             seq_pass, seq_fail);
    $display("p_prop(b or nexttime c), a property, passes %0d fails %0d at ticks",
             prop_pass, prop_fail);
    $display("p_not(b |-> c) passes %0d fails %0d at ticks", not_pass,
             not_fail);
    $display("p_seq(go ##1 b) passes %0d fails %0d at ticks", ante_pass,
             ante_fail);
    $finish;
  end
endmodule
