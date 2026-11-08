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
