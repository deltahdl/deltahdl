// §16.12.1 Property instantiation: an instance of a named property may stand
// as a property_spec, and is legal where the property's body, its actual
// arguments substituted for the formals, is a legal property_spec in that
// place; a body carrying a disable iff clause is a property_spec, legal as
// the whole of an assertion's property though not as the operand of a
// property operator. The assertions below instantiate p_low twice, over
// different actuals, and p_guarded, whose body carries a disable iff, as
// property_specs, and count their passes and failures over four ticks, clk
// rising at 5, 15, 25 and 35 so that tick n is at 10n - 5, the tick counter
// counting through: sig is high at ticks 2 and 3, other at 4 and rst at 2.
//
// low_sig, p_low(sig), passes at 1 and 4 and fails at 2 and 3; low_other,
// p_low(other), passes at 1 to 3 and fails at 4; guarded, p_guarded(sig,
// rst), is disabled at 2, so it passes at 1 and 4 and fails at 3.
module property_instantiation;
  logic clk = 0;
  int tick = 1;
  logic sig, other, rst;
  int sig_pass = 0, sig_fail = 0;
  int other_pass = 0, other_fail = 0;
  int guarded_pass = 0, guarded_fail = 0;
  always #5 clk = ~clk;
  always #10 tick = tick + 1;

  assign sig = tick inside {2, 3};
  assign other = tick inside {4};
  assign rst = tick inside {2};

  property p_low(x);
    @(posedge clk) !x;
  endproperty

  property p_guarded(x, r);
    @(posedge clk) disable iff (r) !x;
  endproperty

  low_sig: assert property (p_low(sig)) sig_pass++; else sig_fail++;
  low_other: assert property (p_low(other)) other_pass++; else other_fail++;
  guarded: assert property (p_guarded(sig, rst))
    guarded_pass++; else guarded_fail++;

  initial begin
    #40;
    $display("p_low(sig) passes %0d fails %0d", sig_pass, sig_fail);
    $display("p_low(other) passes %0d fails %0d", other_pass, other_fail);
    $display("p_guarded(sig, rst) passes %0d fails %0d", guarded_pass,
             guarded_fail);
    $finish;
  end
endmodule
