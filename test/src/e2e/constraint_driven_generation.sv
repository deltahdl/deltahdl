typedef enum {RUNT, PLAIN, JUMBO} kind_t;

class Packet;
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
    static Packet p = new;
    static int legal = 0, solved = 0;
    static bit jumbo_seen = 0;
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
