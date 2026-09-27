// §34.3.1 (printed page 950): --encrypt writes the source text back with each
// encryption envelope replaced by a decryption envelope sealing its body under
// the exchange key given by --protect-key. Every line outside the envelope,
// these comments included, comes back unchanged.
module encrypt_envelope;
`pragma protect data_keyowner="Vendor", data_keyname="k1"
`pragma protect begin
  initial $display("hidden");
`pragma protect end
endmodule
