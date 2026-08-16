module decl_class_scope;
  class Frame;
    typedef byte payload_t;
  endclass

  // §8.23 says a type declared inside a class is public and can be accessed
  // outside the class, so a declaration may name it through the class prefix
  // directly. type_op_class_scope.sv reaches the same typedef through the type
  // operator, which src/elaborator/elaborator_validate_struct_types.cpp
  // resolves on its own; this file is the bare prefix, which reaches the
  // typedef table instead. The pair is what shows the two routes agreeing.
  Frame::payload_t v;

  initial begin
    // byte is 8 bits and signed, so a declaration that lost the Frame prefix
    // prints neither 8 nor -1.
    $display("%0d", $bits(v));
    v = -1;
    $display("%0d", v);
  end
endmodule
