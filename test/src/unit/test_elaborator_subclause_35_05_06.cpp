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

}  // namespace
