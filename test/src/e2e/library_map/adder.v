// The RTL description of adder, which library_map/lib.map's `library rtlLib
// *.v;` maps into rtlLib (IEEE 1800-2023 §33.3.1).
module adder #(parameter W = 8);
  initial $display("rtl adder W=%0d %l", W);
endmodule
