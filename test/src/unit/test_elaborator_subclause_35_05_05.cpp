#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "exported function 'sv_nibble' has a result type "
                            "that is not permitted for DPI",
                            4, "35.5.5"));
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "exported function 'sv_byte' has a result type "
                            "that is not permitted for DPI",
                            4, "35.5.5"));
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "exported function 'sv_count' has a result type "
                            "that is not permitted for DPI",
                            4, "35.5.5"));
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

// §35.5.5: "Function result types are restricted to small values", and a
// typedef name is not a type of its own. Parser::ParseDpiImport holds a result
// written as a name as a kNamed type and ValidateDpiResultType in
// src/parser/parser_dpi_validate.cpp passes every one of them, having no
// typedef table to look the name up in, so the restriction reaches a typedef
// only in the elaborator.
TEST(DpiImportResult, ATypedefOfAPackedVectorAsResultIsError) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      typedef bit [63:0] word_t;
      import "DPI-C" function word_t get_word();
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "imported function 'get_word' has result type "
                            "'word_t', which is not permitted for DPI",
                            4, "35.5.5"));
}

// §35.5.5: a name that stands for a permitted type is permitted, so the
// restriction has to be applied to the type a name reaches rather than to the
// name. Without this case a check that reported every typedef result would
// pass the rejection cases above it.
TEST(DpiImportResult, ATypedefOfAPermittedTypeAsResultIsOk) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      typedef int count_t;
      import "DPI-C" function count_t get_count();
    endmodule
  )",
            f, "m");
  EXPECT_FALSE(f.has_errors);
}

// §35.5.5: a name standing for another name is followed to the end, so writing
// a second typedef over the first does not put a wide vector past the
// restriction. `bit [63:0]` is the type reached, and it is the type judged.
TEST(DpiImportResult, ATypedefChainReachingAPackedVectorAsResultIsError) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      typedef bit [63:0] word_t;
      typedef word_t alias_t;
      import "DPI-C" function alias_t get_word();
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "imported function 'get_word' has result type "
                            "'alias_t', which is not permitted for DPI",
                            5, "35.5.5"));
}

// A result name the enclosing scope does not resolve is left alone, which is
// what src/elaborator/elaborator_dpi.cpp does for a formal argument of an
// unresolved type under §35.5.6. A typedef declared in another module is
// visible to Parser::ParseDataType, which takes every typedef name in the file
// into known_types_, and absent from the map DpiScopeTypedefs builds for this
// module. Reporting it would state a §35.5.5 verdict on a type this check
// never reached.
TEST(DpiImportResult, AResultTypeNameFromAnotherModuleIsLeftAlone) {
  ElabFixture f;
  Elaborate(R"(
    module other;
      typedef bit [63:0] word_t;
    endmodule
    module m;
      import "DPI-C" function word_t get_thing();
    endmodule
  )",
            f, "m");
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "imported function 'get_thing' has result type "
                             "'word_t', which is not permitted for DPI",
                             6, "35.5.5"));
}

// §35.5.5: "The same restrictions apply for the result types of exported
// functions." A name reaches the export path the same way it reaches the
// import path, so the type behind it decides there too.
TEST(DpiExportResult, ExportedFunctionWithTypedefOfPackedVectorResultIsError) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      typedef bit [63:0] word_t;
      function word_t sv_word(); return 64'd0; endfunction
      export "DPI-C" function sv_word;
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "exported function 'sv_word' has a result type "
                            "that is not permitted for DPI",
                            5, "35.5.5"));
}

// §35.5.5: the export path follows a name to a permitted type as readily as to
// a forbidden one, so a function returning a name for `int` still exports.
TEST(DpiExportResult, ExportedFunctionWithTypedefOfIntResultIsOk) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      typedef int count_t;
      function count_t sv_count(); return 0; endfunction
      export "DPI-C" function sv_count;
    endmodule
  )",
            f, "m");
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
