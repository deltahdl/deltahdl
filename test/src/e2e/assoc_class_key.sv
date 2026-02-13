module assoc_class_key;
  class Foo;
    int id;
    function new(int i);
      id = i;
    endfunction
  endclass

  int data[Foo];

  initial begin
    Foo f1, f2;
    f1 = new(1);
    f2 = new(2);
    data[f1] = 10;
    data[f2] = 20;
    $display("%0d", data[f1]);
    $display("%0d", data[f2]);
    $display("%0d", data.size());
  end
endmodule
