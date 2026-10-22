// §6.16 lets a value of the string data type have any length and never
// truncates one, and §11.2.1 lists parameters among the operands a constant
// expression may be built from, so B holds A's ten characters.
//
// Ten characters is what makes the case: a value routed through the 32-bit
// packed number a string declaration falls back to keeps four of them, so a
// truncating fold prints "mith" here and cannot print the whole name by
// accident.
module string_param_named;
  parameter string A = "John Smith";
  parameter string B = A;
  initial $display("%s", B);
endmodule
