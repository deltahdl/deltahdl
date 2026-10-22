// §23.5 Extern modules: a module that has an extern declaration may give .* as
// its port list, which then stands for the extern declaration's ports, and its
// parameters where it has any, written on the module itself. m takes the plain
// port list (a,b,c,d) and a the parameter port list and typed ANSI ports, so
// aa.size is 8 and b is a TP, logic [7:0].
//
// §23.3.1: a top-level module is one the source text holds but no module
// instantiation statement names. top comes before the modules it instantiates:
// with no --top the command line took the last module in the source, a, for the
// top instead, elaborated it alone and printed nothing.
//
// §23.3.2.3 has the declarations on each side of an implicit connection be of
// equivalent data types, so m's one-bit implicit ports meet one-bit wires in
// top, and a's [8:0] a and TP b meet their like in w.
extern module m(a, b, c, d);
extern module a #(parameter size = 8, parameter type TP = logic [7:0])
                (input [size:0] a, output TP b);

module top();
  wire a = 1'b1, b = 1'b0;
  wire c = 1'b1, d;
  m mm(.*);
  w ww();
  initial #1 $display("d %0d", d);
endmodule

module w();
  wire [8:0] a = 9'h101;
  logic [7:0] b;
  a aa(.*);
  initial #2 $display("b %0d size %0d bits %0d", b, aa.size, $bits(b));
endmodule

module m(.*);
  input a, b, c;
  output d;
  assign d = a & c & ~b;
endmodule

module a(.*);
  assign b = a[7:0] + 8'hA9;
endmodule
