// The run makes each file a compilation unit of its own (§3.12.1) and names
// nosuch.sv after this file, and no such file exists. A source that cannot be
// opened fails the run as it does where every file is one unit, so nothing
// below is displayed.
module compilation_unit_per_file_cannot_open;
  initial $display("simulated without nosuch.sv");
endmodule
