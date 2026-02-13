module class_inherit;
  class Base;
    function int get_val();
      return 42;
    endfunction
  endclass

  class Derived extends Base;
    function int get_double();
      return 84;
    endfunction
  endclass

  initial begin
    Derived d;
    d = new();
    $display("%0d", d.get_val());
    $display("%0d", d.get_double());
  end
endmodule
