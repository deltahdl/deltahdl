#include <gtest/gtest.h>

#include "common/types.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(DefaultNettypeElaboration, WireModuleElaboratesCorrectly) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`default_nettype wire\n"
      "module t;\n"
      "  parameter P = 7;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(DefaultNettypeElaboration, NoneWithExplicitDeclsElaborates) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`default_nettype none\n"
      "module t;\n"
      "  wire w;\n"
      "  parameter P = 5;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(DefaultNettypeElaboration, DirectiveControlsImplicitNetType) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`default_nettype wand\n"
      "module top;\n"
      "  assign w = 1'b1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& n : mod->nets) {
    if (n.name == "w") {
      found = true;
      EXPECT_EQ(n.net_type, NetType::kWand);
    }
  }
  EXPECT_TRUE(found) << "implicit net 'w' not created";
}

TEST(DefaultNettypeElaboration, DirectiveControlsPrimitiveTerminalNetType) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`default_nettype tri\n"
      "module top;\n"
      "  and g1(y, a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  int checked = 0;
  for (const auto& n : mod->nets) {
    if (n.name == "y" || n.name == "a" || n.name == "b") {
      ++checked;
      EXPECT_EQ(n.net_type, NetType::kTri);
    }
  }
  EXPECT_EQ(checked, 3) << "implicit gate-terminal nets not all created";
}

struct NoneCase {
  const char* where;
  const char* body;
  const char* name;
  int line;
};

TEST(DefaultNettypeElaboration, NoneReportsAnImplicitNetInEveryPlace) {
  for (const auto& c : {
           NoneCase{"interface assign",
                    "interface i;\n  assign x = 1'b1;\nendinterface\n"
                    "module t; i ii(); endmodule\n",
                    "x", 3},
           NoneCase{"program assign",
                    "program p;\n  assign x = 1'b1;\nendprogram\n"
                    "module t; p pp(); endmodule\n",
                    "x", 3},
           NoneCase{"generate assign",
                    "module t;\n  if (1) begin : g\n    assign x = 1'b1;\n"
                    "  end\nendmodule\n",
                    "x", 4},
           NoneCase{"interface port connection",
                    "interface i(input logic a);\nendinterface\n"
                    "module t;\n  i ii(u);\nendmodule\n",
                    "u", 5},
           NoneCase{"program port connection",
                    "program p(input logic a);\nendprogram\n"
                    "module t;\n  p pp(u);\nendmodule\n",
                    "u", 5},
           NoneCase{"checker port connection",
                    "checker c(logic a);\nendchecker\n"
                    "module t;\n  c cc(u);\nendmodule\n",
                    "u", 5},
       }) {
    ElabFixture f;
    ElaborateWithPreprocessorAllowingParseErrors(
        std::string("`default_nettype none\n") + c.body, f, "", true);
    std::string msg = "implicit net '";
    msg += c.name;
    msg += "' forbidden by `default_nettype none";
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), msg, c.line, "22.8"))
        << c.where;
  }
}

TEST(DefaultNettypeElaboration, DISABLED_NoneReportsAPortExpressionIdentifier) {
  ElabFixture f;
  ElaborateWithPreprocessorAllowingParseErrors(
      "`default_nettype none\nmodule t(input .P(x));\nendmodule\n", f, "",
      true);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "implicit net 'x' forbidden by `default_nettype "
                            "none",
                            2, "22.8"));
}

}  // namespace
