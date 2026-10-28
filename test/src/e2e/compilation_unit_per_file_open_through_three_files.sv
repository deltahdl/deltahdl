// §3.12.1 (printed page 56): with --compilation-unit-per-file a file that ends
// inside a declaration does not end its compilation unit, which extends into
// the files after it until the declaration is complete. Module m opens here,
// middle.sv declares its x and last.sv ends it, so the three files are one
// unit and m elaborates and prints its x.
module m;
