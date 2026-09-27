// §33.8.1: the command line's library search order carries library names and
// nothing else, on a separate-compilation bind as on an invocation that reads
// source descriptions. separate_compilation_bind_search_order_not_a_name.before
// compiles this file into the library `named` and writes it to named.lib, and
// the .args bind it with `-L 9lib`, which is no library name. The bind took
// the argument without a word and bound the design; it now refuses the run as
// lint_only_search_order_not_a_name refuses it on the other path.
module separate_compilation_order_top;
endmodule
