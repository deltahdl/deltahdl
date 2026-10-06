// The run names nosuch.sv after this file, and no such file exists. A source
// named on the command line that cannot be opened fails the run wherever it
// stands in the list, so this file is not simulated alone and nothing below is
// displayed.
module source_file_cannot_open_after_one_that_can;
  initial $display("simulated without nosuch.sv");
endmodule
