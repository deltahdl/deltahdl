module struct_default;
  typedef struct packed {
    logic [7:0] a;
    logic [7:0] b;
  } pair_t;

  pair_t p = '{default: 8'hFF};

  initial begin
    $display("%h", p);
  end
endmodule
