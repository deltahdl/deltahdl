// A.1.2 (printed page 1172) writes source_text as an optional
// timeunits_declaration followed by any number of descriptions, none at all
// among them, so an empty source file is valid source text that adds nothing to
// the design. The run names empty.sv after this file and after.sv after that:
// the empty file is read as empty text, and after.sv is still read, its top
// module instantiating the leaf below and printing.
module source_text_empty_file_leaf;
endmodule
