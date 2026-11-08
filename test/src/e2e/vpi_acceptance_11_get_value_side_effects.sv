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
