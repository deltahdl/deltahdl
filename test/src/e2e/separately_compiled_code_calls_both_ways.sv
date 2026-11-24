module t;
  import "DPI-C" function bit probe_bit(input bit [39:0] vec, input int index);
  import "DPI-C" function logic probe_logic(input logic [3:0] vec, input int index);
  import "DPI-C" function void invert(input bit [31:0] from, output bit [31:0] to);
  import "DPI-C" context function string scope_name();
  import "DPI-C" context function int call_export(input int value);
  import "DPI-C" function int shape(input int a[]);
  export "DPI-C" function sv_twice;
  function int sv_twice(input int value);
    return 2 * value;
  endfunction
  bit [31:0] inverted;
  int q[6:2];
  int r[3];
  initial begin
    $display("bit %0d%0d%0d", probe_bit(40'h80_0000_0004, 39), probe_bit(40'h80_0000_0004, 3),
             probe_bit(40'h80_0000_0004, 2));
    $display("logic %b%b%b%b", probe_logic(4'b10xz, 3), probe_logic(4'b10xz, 2),
             probe_logic(4'b10xz, 1), probe_logic(4'b10xz, 0));
    invert(32'h0f0f_1234, inverted);
    $display("inverted %h", inverted);
    $display("scope %s", scope_name());
    $display("export %0d", call_export(21));
    $display("shape %0d %0d", shape(q), shape(r));
  end
endmodule
