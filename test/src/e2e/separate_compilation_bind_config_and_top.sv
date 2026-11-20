module sc_cfg_top;
  initial $display("design statement top ran");
endmodule

module sc_cfg_spare;
  initial $display("command line top ran");
endmodule

config sc_cfg;
  design sc_cfg_lib.sc_cfg_top;
endconfig
