// §3.12.1 (printed page 56): with --compilation-unit-per-file the files an
// incomplete declaration joins are one compilation unit, so the macro and the
// compilation-unit typedef written here are in force in next.sv, where the
// module this file opens ends: v is 4 bits wide and holds the macro's 4.
`define W 4
typedef logic [3:0] t;
module m;
