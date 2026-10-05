// §37.3.5, §38.15 (printed page 1003, 1100-1101) of IEEE 1800-2023:
// vpi_get_value on an argument expression evaluates it, side effects included,
// once. The library vpi_acceptance_11_get_value_side_effects.c, built beside
// the run and named by vpi_acceptance_11_get_value_side_effects.args, is the
// VPI application under test (#4338).
module top;
  int count;
  function int inc(); count++; return 21; endfunction
  initial begin
    $probe(inc());
    $display("count %0d", count);
    $probe(count * 42);
    $display("count %0d", count);
  end
endmodule
