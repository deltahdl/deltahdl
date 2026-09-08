module class_property_init_alias;
  typedef struct packed {
    logic [7:0] b;
    logic [7:0] l;
  } pair_t;

  pair_t s;

  class C;
    pair_t snap = s;
  endclass

  logic [15:0] got;

  initial begin
    C c;
    s = 16'hAAxB;
    c = new;
    s.b = 8'h00;
    got = c.snap;
    $display("%h", got);
    $display("%h", s);
  end
endmodule
