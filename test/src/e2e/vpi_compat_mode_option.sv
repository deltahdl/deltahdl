// §36.12.2.2: --vpi-compat-mode selects the default VPI compatibility mode of
// the run, which governs every VPI application not bound to a mode when it was
// compiled. It is set before the design is compiled, and a mode the option
// accepts leaves the design compiled and simulated as it is without it.
module vpi_compat_mode_option;
  initial $display("ran under the selected mode");
endmodule
