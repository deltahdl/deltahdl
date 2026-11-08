function int f();
  return 1;
endfunction
module outer;
  function int f();
    return 2;
  endfunction
  module inner;
    initial begin
      $display("%0d", f());
      $finish;
    end
  endmodule
  inner i();
endmodule
