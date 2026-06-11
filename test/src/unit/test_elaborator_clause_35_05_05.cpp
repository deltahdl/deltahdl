#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §35.5.5: "The same restrictions apply for the result types of exported
// functions." A function whose result is a permitted small value (int) can be
// exported without error -- the export's result-type restriction is satisfied.
TEST(DpiExportResult, ExportedFunctionWithSmallValueResultIsOk) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      function int sv_get(); return 0; endfunction
      export "DPI-C" function sv_get;
    endmodule
  )",
            f, "m");
  EXPECT_FALSE(f.has_errors);
}

// §35.5.5: a scalar bit result is a permitted small value, so exporting a
// bit-returning function is well-formed.
TEST(DpiExportResult, ExportedFunctionWithScalarBitResultIsOk) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      function bit sv_flag(); return 1'b0; endfunction
      export "DPI-C" function sv_flag;
    endmodule
  )",
            f, "m");
  EXPECT_FALSE(f.has_errors);
}

// §35.5.5: string is a permitted small-value result, and that permission
// carries over to exported functions, so a string-returning function exports
// without error.
TEST(DpiExportResult, ExportedFunctionWithStringResultIsOk) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      function string sv_name(); return ""; endfunction
      export "DPI-C" function sv_name;
    endmodule
  )",
            f, "m");
  EXPECT_FALSE(f.has_errors);
}

// §35.5.5: the scalar-only restriction on logic results applies to exported
// functions too. A function returning a packed logic vector cannot be exported.
TEST(DpiExportResult, ExportedFunctionWithPackedLogicResultIsError) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      function logic [3:0] sv_nibble(); return 4'h0; endfunction
      export "DPI-C" function sv_nibble;
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(f.has_errors);
}

// §35.5.5: function results are restricted to small values, and that
// restriction carries over to exported functions. A packed bit vector is not a
// scalar bit value, so exporting a function that returns one is an error.
TEST(DpiExportResult, ExportedFunctionWithPackedBitResultIsError) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      function bit [7:0] sv_byte(); return 8'h00; endfunction
      export "DPI-C" function sv_byte;
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(f.has_errors);
}

// §35.5.5: 'integer' is absent from the permitted result-type list (it is a
// wide 4-state vector, allowed only as a formal argument under §35.5.6), so
// exporting an integer-returning function is rejected.
TEST(DpiExportResult, ExportedFunctionWithIntegerResultIsError) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      function integer sv_count(); return 0; endfunction
      export "DPI-C" function sv_count;
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(f.has_errors);
}

// §35.5.5 governs *function* results; a task has no result, so the
// result-type restriction does not constrain an exported task. Exporting a task
// remains well-formed.
TEST(DpiExportResult, ExportedTaskIsNotSubjectToResultRestriction) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      task sv_do(); endtask
      export "DPI-C" task sv_do;
    endmodule
  )",
            f, "m");
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
