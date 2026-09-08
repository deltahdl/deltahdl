module struct_literal_wide;
  typedef struct packed {
    logic [7:0]  a;
    logic [63:0] b;
  } wide_t;

  wide_t known = '{a: 8'hA5, b: 64'h42};
  wide_t unknown = '{a: 8'bxxxxxxxx, b: 64'h42};

  initial begin
    $display("%h", known);
    $display("%h", known.a);
    $display("%h", known.b);
    $display("%h", unknown);
    $display("%h", unknown.a);
  end
endmodule
