// A.2.2.1 lets a data_type name a type_identifier behind a package_scope, and
// A.2.8 lets a data_declaration open the sequential block §9.3.1 describes, so
// the variable below is declared inside `initial begin` as `pkg::nib_t v;` with
// nothing imported: the package name alone carries the type in. The module-
// level twin is decl_class_scope.sv, which reaches a class's typedef through
// its prefix; this file is the block-level position, which the parser decides
// through a different predicate.
// nib_t is 4 bits and unsigned, so a declaration that lost its type prints
// neither 4 nor 15.
package pkg;
  typedef logic [3:0] nib_t;
endpackage

module decl_package_scope_in_block;
  initial begin
    pkg::nib_t v;
    $display("%0d", $bits(v));
    v = -1;
    $display("%0d", v);
  end
endmodule
