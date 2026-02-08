module function_call;
  function integer add(integer a, integer b);
    return a + b;
  endfunction

  function integer double_val(integer x);
    return x + x;
  endfunction

  initial begin
    $display("%d", add(10, 20));
    $display("%d", double_val(7));
    $display("%d", add(add(1, 2), 3));
  end
endmodule
