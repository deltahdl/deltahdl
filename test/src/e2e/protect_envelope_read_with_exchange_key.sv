// §34.3 (printed page 949): "Envelope decryption is the process of
// recognizing decryption envelopes in the input text and transforming them
// into the corresponding cleartext." This envelope was written by
// `deltahdl --encrypt --protect-key K1` from a region naming
// data_keyowner="Vendor" and data_keyname="k1", and is read back here with
// that key, supplied on the command line.
`pragma protect data_keyowner="Vendor", data_keyname="k1"
`pragma protect begin_protected
`pragma protect encrypt_agent="deltahdl"
`pragma protect encrypt_agent_info="SystemVerilog elaborator and protect envelope writer"
`pragma protect data_method="x-deltahdl-stream"
`pragma protect encoding=(enctype="x-deltahdl-block")
`pragma protect data_keyowner="Vendor"
`pragma protect data_keyname="k1"
`pragma protect encoding=(enctype="x-deltahdl-block", bytes=73)
`pragma protect data_block
6rRfFjrQLw_IzRar_tTfenWjmswdgkJNxXmY1HE9kLYMB1W8ANVFWCn8wo6bqb_YuS3GvtcDB-fsvZVXFyGMCLwpOHtJQu2gRg
`pragma protect end_protected
`pragma protect reset
module top; secret s(); endmodule
