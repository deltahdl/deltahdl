#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(BindDirective, CuScopeBindGoesToBindDirectives) {
  auto r = Parse(
      "module target; endmodule\n"
      "module binder; endmodule\n"
      "bind target binder b1();\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_FALSE(r.cu->bind_directives.empty());
}

TEST(BindDirective, BindDirectiveInModule) {
  auto r = Parse(
      "module target; endmodule\n"
      "module checker_m; endmodule\n"
      "module m;\n"
      "  bind target checker_m inst(.*);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(BindDirective, BindDirectiveInInterface) {
  auto r = Parse(
      "module target; endmodule\n"
      "module checker_m; endmodule\n"
      "interface ifc;\n"
      "  bind target checker_m inst(.*);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
