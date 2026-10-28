// §3.12.1 (printed page 56): an identifier is searched for in the nested
// scopes first, a nested module's enclosing module among them (§23.4), and in
// the compilation-unit scope after. With --compilation-unit-per-file each file
// is a unit of its own; this file's unit declares an f returning 1, and the
// module inner, declared inside outer, calls f, which outer declares returning
// 2. inner's call is outer's f and prints 2.
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
