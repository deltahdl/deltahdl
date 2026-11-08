module leaf;
  int v;
  initial #1 $display("%m v %0d", v);
endmodule

module t1;
  int x = 1;
  leaf u();
  initial begin
    u.v = 10;
    #2 $display("%m %0d %0d %0d", x, t2.x, t2.u.v);
  end
endmodule

module t2;
  int x = 2;
  leaf u();
  initial begin
    u.v = 20;
    #3 $display("%m %0d %0d %0d %0d", x, t1.x, t1.u.v, $root.t2.x);
  end
  function int f();
    return x * 100;
  endfunction
endmodule

module t3;
  initial #4 $display("%m %0d %0d", t2.f(), $root.t1.x);
endmodule
