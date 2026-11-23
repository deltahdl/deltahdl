#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "parser/ast_module.h"

using namespace delta;

namespace {

TEST(OperatorOverloadingDeprecated, BindOfBinaryOperatorIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  bind + function int add(int a, int b);\n"
      "  int x;\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "operator overloading has been removed", 2,
                            "C.2.8"));
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(r.cu->modules[0]->bind_directives.empty());
  EXPECT_TRUE(HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kVarDecl));
}

TEST(OperatorOverloadingDeprecated, BindOfAssignmentOperatorAtUnitScope) {
  auto r = Parse(
      "bind = function int conv(real r);\n"
      "module m; endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "operator overloading has been removed", 1,
                            "C.2.8"));
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(r.cu->bind_directives.empty());
  EXPECT_EQ(r.cu->modules.size(), 1u);
}

TEST(OperatorOverloadingDeprecated, EveryOverloadableOperatorIsRejected) {
  const char* const kOperators[] = {"+",  "++", "-", "--", "*", "**", "/", "%",
                                    "==", "!=", "<", "<=", ">", ">=", "="};
  for (const char* op : kOperators) {
    auto r = Parse(std::string("module m;\n  bind ") + op +
                   " function int f(int a);\nendmodule\n");
    EXPECT_TRUE(ReportedError(r.diags, "operator overloading has been removed",
                              2, "C.2.8"))
        << op;
  }
}

TEST(OperatorOverloadingDeprecated, BindDirectiveStillParses) {
  auto r = Parse(
      "module target; endmodule\n"
      "module binder; endmodule\n"
      "module m;\n"
      "  bind target binder b1();\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 3u);
  EXPECT_EQ(r.cu->modules[2]->bind_directives.size(), 1u);
}

TEST(OperatorOverloadingDeprecated, BindOfAnOperatorInEveryOtherScope) {
  const char* const kScopes[][2] = {
      {"package pk;\n", "endpackage\n"},
      {"interface ifc;\n", "endinterface\n"},
      {"program p;\n", "endprogram\n"},
      {"module m;\n  if (1) begin : g\n", "  end\nendmodule\n"},
      {"checker chk;\n", "endchecker\n"},
  };
  for (const auto& scope : kScopes) {
    std::string src = scope[0];
    src += "  bind + function int add(int a, int b);\n";
    src += scope[1];
    auto r = Parse(src);
    const uint32_t kLine = LineHolding(src, "bind");
    EXPECT_TRUE(ReportedError(r.diags, "operator overloading has been removed",
                              kLine, "C.2.8"))
        << src;
  }
}

TEST(OperatorOverloadingDeprecated,
     BindDirectiveStillParsesInAnInterfaceAndAGenerateBlock) {
  const char* const kScopes[][2] = {
      {"interface ifc;\n", "endinterface\n"},
      {"module m;\n  if (1) begin : g\n", "  end\nendmodule\n"},
  };
  for (const auto& scope : kScopes) {
    std::string src = "module binder;\nendmodule\nmodule target;\nendmodule\n";
    src += scope[0];
    src += "  bind target binder b1 ();\n";
    src += scope[1];
    auto r = Parse(src);
    EXPECT_FALSE(r.has_errors) << src;
  }
}

}  // namespace
