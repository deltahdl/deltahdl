// §18.1 General: the clause describes random variables, constraint blocks,
// randomization methods, disabling randomization, controlling constraints,
// scope variable randomization, seeding the random number generator,
// random weighted case statements and random sequence generation, one
// tour of which this design takes, each stop printing what the rules of
// the subclause describing it determine and never a value the generator
// chose. The Bus of §18.3 carries the random variables addr and data and
// the constraint block word_align, so addr's two low-order bits are 0
// after every randomize(); randomize() answers 1 for a solvable problem
// and its with clause adds a constraint, addr == 8; data.rand_mode(0)
// leaves data at the 99 written before the next randomize();
// word_align.constraint_mode(0) lets an in-line addr == 3 be solved;
// std::randomize(v) with a range constrains the scope variable v to it;
// two objects seeded alike through srandom draw the same addr; a randcase
// whose second branch weighs 0 takes the first; and a randsequence runs
// its productions in order.
class Bus;
  rand bit [15:0] addr;
  rand bit [31:0] data;
  constraint word_align { addr[1:0] == 2'b0; }
endclass

module constrained_random_overview;
  initial begin
    Bus bus = new;
    Bus other = new;
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
