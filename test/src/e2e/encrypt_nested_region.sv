// §34.5.1 (printed page 953) makes a begin opened inside a begin-end region that
// is still open an error. --encrypt reports it, writes the encrypted text anyway,
// and exits with status 1.
module encrypt_nested_region;
`pragma protect begin
`pragma protect begin
  initial $display("hidden");
`pragma protect end
endmodule
