#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

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

TEST(DpiExportResult, ExportedFunctionWithTypedefOfIntResultIsOk) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      typedef int count_t;
      function count_t sv_count(); endfunction
      export "DPI-C" function sv_count;
    endmodule
  )",
            f, "m");
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
