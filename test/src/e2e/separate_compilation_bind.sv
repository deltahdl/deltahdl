module separate_compilation_top;
  separate_compilation_leaf u();
endmodule

module separate_compilation_leaf;
endmodule

config separate_compilation_cfg;
  design cells.separate_compilation_top;
endconfig
