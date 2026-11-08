class Bus;
  rand bit [15:0] addr;
  rand bit [31:0] data;
  constraint word_align { addr[1:0] == 2'b0; }
endclass

module constrained_random_overview;
  initial begin
    static Bus bus = new;
    static Bus other = new;
    int v;
    int taken;
    bit ok;
    $display("randomize returns %0d", bus.randomize());
    $display("addr[1:0] == %0d after randomize", bus.addr[1:0]);
    ok = bus.randomize() with { addr == 8; };
    $display("with: addr == 8 holds %0d", ok && bus.addr == 8);
    bus.data.rand_mode(0);
    bus.data = 99;
    void'(bus.randomize());
    $display("rand_mode(0): data stays %0d", bus.data);
    bus.word_align.constraint_mode(0);
    ok = bus.randomize() with { addr == 3; };
    $display("constraint_mode(0): addr == 3 holds %0d", ok && bus.addr == 3);
    bus.word_align.constraint_mode(1);
    ok = std::randomize(v) with { v inside {[10:12]}; };
    $display("std::randomize: v in [10:12] holds %0d", ok && v >= 10 && v <= 12);
    bus.data.rand_mode(1);
    bus.srandom(42);
    other.srandom(42);
    void'(bus.randomize());
    void'(other.randomize());
    $display("srandom(42) twice: same addr %0d", bus.addr == other.addr);
    randcase
      1: taken = 1;
      0: taken = 2;
    endcase
    $display("randcase weights 1 and 0: taken %0d", taken);
    randsequence(main)
      main : first second;
      first : { $write("randsequence: first"); };
      second : { $display(" then second"); };
    endsequence
    $finish;
  end
endmodule
