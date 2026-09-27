// §23.3.1: "A top-level module is implicitly instantiated once, and its
// instance name is the same as the module name", and each such instance is a
// scope of its own (§23.9), so t1 and t2 each hold their own x and their own
// instance u. §23.6 reaches one from the other by the complete path, t2.x and
// t1.u.v, a call through it runs in the named top, t2.f() reading t2's x,
// and $root.t2.x is t2's x from inside t2 itself. %m names the instance a
// process runs in from the top it stands under. The tops' declarations were
// stored under one name each, the last top's replacing the first's, so both
// tops read t2's values.
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
