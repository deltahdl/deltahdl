#include <gtest/gtest.h>

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ClassParsing, WeakRefClearCallParses) {
  EXPECT_TRUE(
      ParseOk("class obj;\n"
              "  int x;\n"
              "endclass\n"
              "module m;\n"
              "  initial begin\n"
              "    obj strong_obj;\n"
              "    weak_reference #(obj) wr;\n"
              "    strong_obj = new();\n"
              "    wr = new(strong_obj);\n"
              "    wr.clear();\n"
              "  end\n"
              "endmodule\n"));
}

}  // namespace
