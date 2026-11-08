module separate_compilation_runs_top;
  separate_compilation_runs_leaf #(.W(4)) u();
endmodule

module separate_compilation_runs_leaf #(parameter W = 8);
  initial $display("bound leaf W=%0d", W);
endmodule

config separate_compilation_runs_cfg;
  design runs.separate_compilation_runs_top;
endconfig
