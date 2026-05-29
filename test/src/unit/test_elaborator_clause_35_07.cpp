#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §35.7: an export declaration's c_identifier is optional; when omitted it
// defaults to the SystemVerilog function_identifier. The elaborator therefore
// accepts an export declaration with no explicit c_identifier.
TEST(DpiExportElab, OmittedCIdentifierDefaultsToFunctionIdentifier) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      function void sv_func(); endfunction
      export "DPI-C" function sv_func;
    endmodule
  )",
            f, "m");
  EXPECT_FALSE(f.has_errors);
}

// §35.7: "No two functions in the same SystemVerilog scope can be exported
// with the same explicit or implicit c_identifier." Two export declarations
// in one module that share an explicit c_identifier collide.
TEST(DpiExportElab, DuplicateExplicitCIdentifierInSameScopeIsError) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      function void sv_a(); endfunction
      function void sv_b(); endfunction
      export "DPI-C" link = function sv_a;
      export "DPI-C" link = function sv_b;
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(f.has_errors);
}

// §35.7: "The export declaration and the definition of the corresponding
// SystemVerilog function can occur in any order." Placing the export
// declaration before the function definition is well-formed.
TEST(DpiExportElab, ExportBeforeFunctionDefinitionInSameScopeIsOk) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      export "DPI-C" function sv_func;
      function void sv_func(); endfunction
    endmodule
  )",
            f, "m");
  EXPECT_FALSE(f.has_errors);
}

// §35.7: "Only one export declaration is permitted per SystemVerilog
// function." Two exports of the same SV function with distinct c_identifiers
// would slip through a c_identifier-only collision check, so the elaborator
// also dedupes on the underlying SystemVerilog routine.
TEST(DpiExportElab, TwoExportsOfSameSvFunctionWithDifferentCIdsIsError) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      function void sv_func(); endfunction
      export "DPI-C" first = function sv_func;
      export "DPI-C" second = function sv_func;
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(f.has_errors);
}

// §35.7: an exported SystemVerilog function must obey the same restrictions
// on argument types as an imported function. The §35.5.4 prohibition on the
// ref qualifier in DPI declarations carries through, so a function with a
// ref argument cannot be exported.
TEST(DpiExportElab, ExportedFunctionWithRefArgumentIsError) {
  ElabFixture f;
  Elaborate(R"(
    module m;
      function void sv_func(ref int x); endfunction
      export "DPI-C" function sv_func;
    endmodule
  )",
            f, "m");
  EXPECT_TRUE(f.has_errors);
}

}  // namespace
