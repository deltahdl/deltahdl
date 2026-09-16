// §18.3 Concepts and usage: random stimulus is generated within objects,
// whose random variables take values subject to user-defined constraints.
// The clause's Bus carries the random addr and data and the word_align
// constraint, and calling randomize() selects new values for all of its
// random variables such that all of its constraints are satisfied, data,
// unconstrained, taking any value in its declared range; MyBus extends
// Bus, inheriting its random variables and constraints and adding the
// random atype, whose addr_range constraint selects one of three address
// ranges by implication, so that a randomized MyBus has addr, data and
// atype computed together; randomize() with declares additional
// constraints in line, the clause's exercise_bus restricting atype to low,
// addr to 10 to 20 and data to the powers of two; the solver handles
// algebraic factoring, complex Boolean expressions and mixed integer and
// bit expressions, the power-of-two constraint written arithmetically or
// as 1 << n with n a 5-bit random variable; if a solution exists the
// solver finds it; the chosen values satisfy all constraints, an
// implication's among them; an enum random variable takes only a named
// constant; and constraint_mode() disables a named constraint block, the
// clause's exercise_illegal randomizing with the low-order address bits
// forced nonzero. Every line prints how many of the randomizations met
// what the rules determine and never a value the generator chose.
class Bus;
  rand bit [15:0] addr;
  rand bit [31:0] data;
  constraint word_align { addr[1:0] == 2'b0; }
endclass

typedef enum {low, mid, high} AddrType;

class MyBus extends Bus;
  rand AddrType atype;
  constraint addr_range {
    (atype == low) -> addr inside { [0 : 15] };
    (atype == mid) -> addr inside { [16 : 127] };
    (atype == high) -> addr inside { [128 : 255] };
  }
endclass

class PowerOfTwo;
  rand bit [4:0] n;
  rand bit [31:0] d;
  constraint shifted { d == 1 << n; }
endclass

module constrained_random_concepts;
  function bit in_range(MyBus b);
    case (b.atype)
      low: in_range = b.addr <= 15;
      mid: in_range = b.addr >= 16 && b.addr <= 127;
      high: in_range = b.addr >= 128 && b.addr <= 255;
      default: in_range = 0;
    endcase
  endfunction

  task exercise_bus(MyBus bus, output int met);
    int res;
    met = 0;
    res = bus.randomize() with {atype == low;};
    met += res && bus.atype == low && bus.addr <= 15 && bus.addr[1:0] == 0;
    res = bus.randomize() with {10 <= addr && addr <= 20;};
    met += res && bus.addr >= 10 && bus.addr <= 20 && bus.addr[1:0] == 0;
    res = bus.randomize() with {(data & (data - 1)) == 0;};
    met += res && (bus.data & (bus.data - 1)) == 0;
  endtask

  initial begin
    Bus bus = new;
    MyBus mybus = new;
    PowerOfTwo p2 = new;
    int ok, aligned, ranged, met;
    ok = 0; aligned = 0;
    repeat (50) begin
      if (bus.randomize() == 1) ok++;
      if (bus.addr[1:0] == 2'b0) aligned++;
    end
    $display("Bus: %0d of 50 randomized, %0d of 50 word aligned", ok, aligned);
    ok = 0; aligned = 0; ranged = 0;
    repeat (30) begin
      if (mybus.randomize() == 1) ok++;
      if (mybus.addr[1:0] == 2'b0) aligned++;
      if (in_range(mybus)) ranged++;
    end
    $display("MyBus: %0d of 30 randomized, %0d of 30 word aligned, %0d of 30 in the range atype selects", ok, aligned, ranged);
    exercise_bus(mybus, met);
    $display("exercise_bus: %0d of 3 in-line constraints met", met);
    ok = 0;
    repeat (10) if (p2.randomize() == 1 && p2.d == (1 << p2.n)) ok++;
    $display("PowerOfTwo: %0d of 10 have d == 1 << n", ok);
    mybus.word_align.constraint_mode(0);
    ok = mybus.randomize() with {addr[0] || addr[1];};
    $display("word_align off: randomized %0d, low bits nonzero %0d", ok, mybus.addr[1:0] != 0);
    mybus.word_align.constraint_mode(1);
    ok = mybus.randomize();
    $display("word_align on: randomized %0d, word aligned %0d", ok, mybus.addr[1:0] == 0);
    $finish;
  end
endmodule
