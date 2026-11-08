package pkg;
  typedef logic [3:0] nib_t;
endpackage

module decl_package_scope_in_block;
  initial begin
    pkg::nib_t v;
    $display("%0d", $bits(v));
    v = -1;
    $display("%0d", v);
  end
endmodule
