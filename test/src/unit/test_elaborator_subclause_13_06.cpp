#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(ImportedSubroutineCallElaboration,
     AnImportsOutputActualThatIsNoVariableIsReportedAsANativeOnesIs) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  import \"DPI-C\" function void store(input int a, output int o);\n"
      "  import \"DPI-C\" task twice(input int a, output int o);\n"
      "  int r;\n"
      "  initial begin\n"
      "    store(1, 5);\n"
      "    twice(1, r + 1);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "output argument 'o' requires a variable", 6,
                            "13.5"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "output argument 'o' requires a variable", 7,
                            "13.5"));
}

TEST(ImportedSubroutineCallElaboration,
     AnImportsOutputActualThatIsAVariableIsAcceptedAsANativeOnesIs) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  import \"DPI-C\" function void store(input int a, output int o);\n"
      "  import \"DPI-C\" task twice(input int a, output int o);\n"
      "  int r, a[2];\n"
      "  initial begin\n"
      "    store(1, r);\n"
      "    twice(1, a[1]);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ImportedSubroutineCallElaboration,
     AnImportedTaskUsedAsAnOperandIsReportedAsANativeOneIs) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  import \"DPI-C\" task twice(input int a, output int o);\n"
      "  int r;\n"
      "  initial r = twice(1, r);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "task 'twice' is enabled from a statement and "
                            "cannot be an operand of an expression",
                            4, "13.3"));
}

}  // namespace
