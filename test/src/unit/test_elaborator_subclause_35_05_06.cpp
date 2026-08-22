#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// §35.5.6: "In exported DPI subroutines, it is erroneous to declare formal
// arguments of dynamic array types." A function whose formal argument is a
// dynamic array (the unsized "[]" form) cannot be exported for DPI.
TEST(DpiExportFormalType, ExportedFunctionWithDynamicArrayArgIsError) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      function void sv_take(input int data[]); endfunction
      export "DPI-C" function sv_take;
    endmodule
  )",
            f, "m");
  // The report stands at the export declaration, line 4 of the literal above,
  // whose first line is the newline that follows R"(.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "SystemVerilog function 'sv_take' has a dynamic "
                            "array formal argument and therefore cannot be "
                            "exported for DPI",
                            4, "35.5.6"));
}

// §35.5.6: the dynamic-array prohibition on exported subroutines applies to
// tasks as well as functions, since both are DPI subroutines. §35.8 terms such
// a subroutine an exported task, so the report names the word the declaration
// used rather than calling it a function.
TEST(DpiExportFormalType, ExportedTaskWithDynamicArrayArgSaysTask) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      task sv_consume(input byte stream[]); endtask
      export "DPI-C" task sv_consume;
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "SystemVerilog task 'sv_consume' has a dynamic "
                            "array formal argument and therefore cannot be "
                            "exported for DPI",
                            4, "35.5.6"));
}

// §35.5.6: the prohibition is specific to *dynamic* arrays. A fixed-size
// unpacked array is a permitted construct for a DPI formal argument, so an
// export carrying one is well-formed -- confirming the check keys on the
// unsized dynamic-array form and not on unpacked dimensions in general.
TEST(DpiExportFormalType, ExportedFunctionWithFixedUnpackedArrayArgIsOk) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      function void sv_take(input int data[4]); endfunction
      export "DPI-C" function sv_take;
    endmodule
  )",
            f, "m");
  EXPECT_FALSE(f.has_errors);
}

// §35.5.6: a plain scalar formal argument is among the permitted types and
// carries no unpacked dimension, so it does not trip the dynamic-array rule.
TEST(DpiExportFormalType, ExportedFunctionWithScalarArgIsOk) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      function void sv_take(input int value); endfunction
      export "DPI-C" function sv_take;
    endmodule
  )",
            f, "m");
  EXPECT_FALSE(f.has_errors);
}

// §35.5.6: the prohibition applies to every formal argument, so a dynamic array
// is rejected even when it is not the first argument and is preceded by
// permitted ones.
TEST(DpiExportFormalType,
     ExportedFunctionWithDynamicArrayArgAmongOthersIsError) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      function void sv_take(input int ok, input int data[]); endfunction
      export "DPI-C" function sv_take;
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "SystemVerilog function 'sv_take' has a dynamic "
                            "array formal argument and therefore cannot be "
                            "exported for DPI",
                            4, "35.5.6"));
}

// §35.5.6: "The following SystemVerilog types are the only permitted types for
// formal arguments of import and export subroutines". An event is not among
// them, so an export whose subroutine takes one is rejected.
TEST(DpiExportFormalType, ExportedFunctionWithEventArgIsError) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      function void sv_notify(input event ev); endfunction
      export "DPI-C" function sv_notify;
    endmodule
  )",
            f, "m");
  // The report stands at the export declaration, line 4 of the literal above,
  // whose first line is the newline that follows R"(.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "SystemVerilog function 'sv_notify' has a formal "
                            "argument 'ev' whose type is not permitted for DPI",
                            4, "35.5.6"));
}

// §35.5.6: the permitted set governs the formal arguments of every DPI
// subroutine, tasks as well as functions. The report names the word the
// declaration used, so a user who wrote a task is not sent looking for a
// function they never declared.
TEST(DpiExportFormalType, ExportedTaskWithEventArgSaysTask) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      task sv_wait(input event ev); endtask
      export "DPI-C" task sv_wait;
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "SystemVerilog task 'sv_wait' has a formal "
                            "argument 'ev' whose type is not permitted for DPI",
                            4, "35.5.6"));
}

// §35.5.6 admits a union in its packed form only, so an exported subroutine
// whose formal argument is an unpacked union is rejected.
TEST(DpiExportFormalType, ExportedFunctionWithUnpackedUnionArgIsError) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      function void sv_take(input union { byte b; int i; } u); endfunction
      export "DPI-C" function sv_take;
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "SystemVerilog function 'sv_take' has an unpacked union "
                    "formal argument 'u'; only the packed form of a union is "
                    "permitted for DPI",
                    4, "35.5.6"));
}

// §35.5.6: the packed form of a union is a permitted type, so the same export
// stands once the union is declared packed -- confirming the check keys on the
// packing and not on the union keyword.
TEST(DpiExportFormalType, ExportedFunctionWithPackedUnionArgIsOk) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      function void sv_take(
          input union packed { bit [7:0] a; logic [7:0] b; } u);
      endfunction
      export "DPI-C" function sv_take;
    endmodule
  )",
            f, "m");
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
