// §16.12.18 Typed formal arguments in property declarations: the rules of
// §16.8.1 for typed formal arguments apply to a named property, so a formal
// typed with a data type takes its actual cast to that type and a formal of
// type event takes an event expression; and a formal may be of type
// property, in which case its actual is a property_expr, a boolean or a
// sequence_expr being one, and each reference to it stands where a
// property_expr may. A formal of type sequence takes a sequence_expr. The
// assertions below run over eight ticks, clk rising at 5, 15, ..., 75 so
// that tick n is at 10n - 5: v is 8'h02 at 2 and 4 and 8'h01 at 6, w is high
// at 2 and 6, go at 1, 3, 5 and 7, b at 2, 3, 6, 7 and 8, and c at 2 and 4.
//
// untyped and typed are p_untyped and p_bit, alike but for p_bit typing x
// as bit: x untyped reads v whole, high at 2, 4 and 6, where w fails it at
// 4; x a bit reads the low bit of v, high at 6 alone, where w holds. ev is
// p_ev with the event posedge clk as its actual, and sig p_sig with clk as
// the signal under the edge its clock writes; both check w after v == 2
// and fail at 4. prop_bool, prop_seq and prop_prop pass a boolean, a
// sequence and a property to p_prop's formal of type property, the
// consequent after go: b fails at 1 and 5; b ##1 c fails at 1 and 5 with
// b low and at 8 with c low after 7; b or nexttime c fails at 6 alone,
// with b low and c low a tick later. negated passes b |-> c to p_not,
// whose body negates its formal: the implication holds at every tick but
// 3, 6, 7 and 8, where b is high and c low, so the negation holds at
// those four. seq_ante passes go ##1 b to p_seq's formal of type
// sequence, the antecedent of its implication: the antecedent matches at
// 2, 6 and 8, a tick after go, and c fails it at 6 and 8.
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
