#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(BuiltinMethodElaboration, AssocArrayNumOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int assoc [string];\n"
             "  int n;\n"
             "  initial n = assoc.num();\n"
             "endmodule\n"));
}

TEST(BuiltinMethodElaboration, AssocArraySizeOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int assoc [string];\n"
             "  int n;\n"
             "  initial n = assoc.size();\n"
             "endmodule\n"));
}

}  // namespace
