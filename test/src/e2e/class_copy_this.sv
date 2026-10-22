// A shallow copy whose source is `this`. IEEE 1800-2023 §8.11 makes the keyword
// a built-in handle to the object through which the enclosing subroutine was
// invoked, and footnote 23 on A.2.4's class_new asks only that a copy source
// yield an object handle, so `new this` copies the object copied_x was called
// on.
//
// 42 is the number that tells the behaviours apart. §8.12 step 1 has the
// allocation leave the object's constructor uncalled, so a copy prints the 42
// the caller assigned; a run that constructed instead prints the 7 the
// constructor writes, and one that allocated without constructing prints the
// declared default 0.
module class_copy_this;
  class C;
    int x;
    function new();
      x = 7;
    endfunction
    function int copied_x();
      C copy;
      copy = new this;
      return copy.x;
    endfunction
  endclass

  initial begin
    C p;
    p = new();
    p.x = 42;
    $display("%0d", p.copied_x());
  end
endmodule
