// §18.2 Overview: constraint-driven test generation lets a test bench
// generate its stimulus, the constraints written in a compact declarative
// way and processed by a solver that generates random values meeting
// them, which can reach corner cases a directed test would miss; the
// constraints are specified on top of an object-oriented data
// abstraction that models the data to be randomized as objects holding
// random variables and user-defined constraints, which determine the
// legal values, objects being ideal for complex aggregate data such as
// Ethernet packets. The Packet here is such an abstraction: its random
// kind, length and tag are legal only where the constraints allow, a
// runt being shorter than 64, a jumbo longer than 1518, a plain frame
// in between, the tag set only on a plain frame, and its corner
// constraint making a jumbo as long as it can be. Each of 24 randomize()
// calls yields legal values, every value is checked against the same
// constraints and the count of those meeting them is printed, as is the
// corner the constraints reach without a directed test naming it.
class Packet;
  typedef enum {RUNT, PLAIN, JUMBO} kind_t;
  rand kind_t kind;
  rand int length;
  rand bit tag;
  constraint legal {
    kind == RUNT -> length inside {[1:63]};
    kind == PLAIN -> length inside {[64:1518]};
    kind == JUMBO -> length == 9000;
    tag -> kind == PLAIN;
  }
  function bit meets_constraints();
    case (kind)
      RUNT: meets_constraints = length >= 1 && length <= 63 && !tag;
      PLAIN: meets_constraints = length >= 64 && length <= 1518;
      JUMBO: meets_constraints = length == 9000 && !tag;
    endcase
  endfunction
endclass

module constraint_driven_generation;
  initial begin
    Packet p = new;
    int legal = 0, solved = 0;
    bit jumbo_seen = 0;
    repeat (24) begin
      if (p.randomize()) solved++;
      if (p.meets_constraints()) legal++;
    end
    $display("solved %0d of 24, legal %0d of 24", solved, legal);
    void'(p.randomize() with { kind == JUMBO; });
    $display("corner: a jumbo is %0d long with tag %0d", p.length, p.tag);
    $finish;
  end
endmodule
