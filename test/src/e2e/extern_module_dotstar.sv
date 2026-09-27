// §23.5 Extern modules: "If an extern declaration exists for a module, it is
// possible to use .* as the ports of the module. This usage shall be
// equivalent to placing the ports (and possibly parameters) of the extern
// declaration on the module." m takes the plain port list (a,b,c,d) and a the
// parameter port list and typed ANSI ports, so aa.size is 8 and b is a TP,
// logic [7:0].
//
// §23.3.1: "Top-level modules are modules that are included in the
// SystemVerilog source text, but do not appear in any module instantiation
// statement". top comes before the modules it instantiates: with no --top the
// command line took the last module in the source, a, for the top instead,
// elaborated it alone and printed nothing.
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
