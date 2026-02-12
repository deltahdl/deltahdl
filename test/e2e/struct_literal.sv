module struct_literal;
  typedef struct packed {
    logic [7:0] x;
    logic [7:0] y;
  } point_t;

  point_t p = '{x: 8'hAA, y: 8'hBB};

  initial begin
    $display("%h", p);
    $display("%h", p.x);
    $display("%h", p.y);
  end
endmodule
