#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "elaborator/type_eval.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;
namespace {

TEST(VoidDataType, VoidTypeWidthIsZero) {
  DataType dt;
  dt.kind = DataTypeKind::kVoid;
  EXPECT_EQ(EvalTypeWidth(dt), 0u);
}

TEST(VoidDataType, VoidNotIntegral) {
  EXPECT_FALSE(IsIntegralType(DataTypeKind::kVoid));
}

TEST(VoidDataType, VoidNot4State) {
  EXPECT_FALSE(Is4stateType(DataTypeKind::kVoid));
}

TEST(VoidDataType, VoidFunctionReturnsValue_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  function void bad();\n"
      "    return 1;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "void function returns a value", 3, "13.4.1"));
}

TEST(VoidDataType, VoidFunctionBareReturn_Ok) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  function void ok_func();\n"
      "    return;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(VoidDataType, VoidFunctionNoReturn_Ok) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  function void ok_func();\n"
      "    $display(\"done\");\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(VoidDataType, VoidFunctionNestedReturnValue_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  function void bad();\n"
      "    begin\n"
      "      return 7;\n"
      "    end\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "void function returns a value", 4, "13.4.1"));
}

TEST(VoidDataType, VoidFunctionConditionalBareReturn_Ok) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  function void ok_func();\n"
      "    if (1) return;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(VoidDataType, VoidMemberInTaggedUnion_Ok) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  typedef union tagged { void Invalid; int Valid; } VInt;\n"
      "  VInt u;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(VoidDataType, SoleVoidMemberInTaggedUnion_Ok) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  typedef union tagged { void None; } Opt;\n"
      "  Opt u;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(VoidDataType, VoidMemberInPackedTaggedUnion_Ok) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  typedef union tagged packed { void Invalid; bit [31:0] Valid; } "
      "VInt;\n"
      "  VInt u;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

::testing::AssertionResult ReportedOn(const std::string& src,
                                      std::string_view marker,
                                      std::string_view message,
                                      std::string_view subclause) {
  ElabFixture f;
  ElaborateSrc(src, f);
  return ReportedError(f.diag.Diagnostics(), message, LineHolding(src, marker),
                       subclause);
}

constexpr std::string_view kReturnsAValue = "void function returns a value";
constexpr std::string_view kUsedAsOperand = "used as expression operand";

TEST(VoidDataType, ValueReturnedFromAVoidFunctionIsReportedInEveryOtherPlace) {
  const char* const kSources[] = {
      "interface i;\n  function void f();\n    return 4;\n  endfunction\n"
      "endinterface\nmodule t;\n  i u();\nendmodule\n",
      "program p;\n  function void f();\n    return 4;\n  endfunction\n"
      "endprogram\nmodule t;\n  p u();\nendmodule\n",
      "checker c(logic clk);\n  function void f();\n    return 4;\n"
      "  endfunction\nendchecker\nmodule t;\n  logic clk;\n  c u(clk);\n"
      "endmodule\n",
      "class C;\n  static function void f();\n    return 4;\n  endfunction\n"
      "endclass\nmodule t;\nendmodule\n",
      "module t;\n  if (1) begin : g\n    function void f();\n"
      "      return 4;\n    endfunction\n  end\nendmodule\n",
      "module t;\n  function automatic void f();\n    return 4;\n"
      "  endfunction\nendmodule\n",
  };
  for (const char* src : kSources) {
    SCOPED_TRACE(src);
    EXPECT_TRUE(ReportedOn(src, "return 4", kReturnsAValue, "13.4.1"));
  }
}

TEST(VoidDataType,
     DISABLED_ValueReturnedFromAVoidFunctionIsReportedInPackageAndUnit) {
  EXPECT_TRUE(ReportedOn(
      "package k;\n  function void f();\n    return 4;\n  endfunction\n"
      "endpackage\nmodule t;\nendmodule\n",
      "return 4", kReturnsAValue, "13.4.1"));
  EXPECT_TRUE(ReportedOn(
      "function void f();\n  return 4;\nendfunction\nmodule t;\nendmodule\n",
      "return 4", kReturnsAValue, "13.4.1"));
}

TEST(VoidDataType, BareReturnFromAVoidFunctionIsAcceptedInEveryPlace) {
  EXPECT_TRUE(
      ElabOk("package k;\n  function void f();\n    return;\n  endfunction\n"
             "endpackage\nfunction void uf();\n  return;\nendfunction\n"
             "interface i;\n  function void f();\n    return;\n"
             "  endfunction\nendinterface\nprogram p;\n"
             "  function void f();\n    return;\n  endfunction\nendprogram\n"
             "class C;\n  function void f();\n    return;\n  endfunction\n"
             "endclass\nmodule t;\n  i u();\n  p v();\n"
             "  if (1) begin : g\n    function void f();\n      return;\n"
             "    endfunction\n  end\nendmodule\n"));
}

TEST(VoidDataType, VoidFunctionCallAsAnOperandIsReportedInAModuleOrInterface) {
  EXPECT_TRUE(
      ReportedOn("module t;\n  function void f();\n  endfunction\n  int x;\n"
                 "  initial x = f() + 1;\nendmodule\n",
                 "x = f()", kUsedAsOperand, "13.4.1"));
  EXPECT_TRUE(
      ReportedOn("module t;\n  function void f();\n  endfunction\n  int x;\n"
                 "  initial if (f()) x = 1;\nendmodule\n",
                 "if (f())", kUsedAsOperand, "13.4.1"));
  EXPECT_TRUE(ReportedOn(
      "interface i;\n  function void f();\n  endfunction\n  int x;\n"
      "  initial x = f();\nendinterface\nmodule t;\n  i u();\nendmodule\n",
      "x = f()", kUsedAsOperand, "13.4.1"));
}

TEST(VoidDataType,
     DISABLED_VoidFunctionCallAsAnOperandIsReportedInPackageClassAndUnit) {
  EXPECT_TRUE(ReportedOn(
      "package k;\n  function void f();\n  endfunction\n"
      "  function int g();\n    return f();\n  endfunction\nendpackage\n"
      "module t;\nendmodule\n",
      "return f()", kUsedAsOperand, "13.4.1"));
  EXPECT_TRUE(ReportedOn(
      "class C;\n  function void f();\n  endfunction\n"
      "  function int g();\n    return f() + 1;\n  endfunction\nendclass\n"
      "module t;\nendmodule\n",
      "return f()", kUsedAsOperand, "13.4.1"));
  EXPECT_TRUE(
      ReportedOn("function void f();\nendfunction\nfunction int g();\n"
                 "  return f();\nendfunction\nmodule t;\nendmodule\n",
                 "return f()", kUsedAsOperand, "13.4.1"));
  EXPECT_TRUE(
      ReportedOn("package k;\n  function void f();\n  endfunction\nendpackage\n"
                 "module t;\n  int y;\n  initial y = k::f();\nendmodule\n",
                 "k::f()", kUsedAsOperand, "13.4.1"));
}

TEST(VoidDataType, VoidFunctionCallAsAStatementIsAcceptedInEveryPlace) {
  EXPECT_TRUE(
      ElabOk("package k;\n  function void f();\n  endfunction\n"
             "  function int g();\n    f();\n    return 1;\n  endfunction\n"
             "endpackage\nclass C;\n  function void f();\n  endfunction\n"
             "  function int g();\n    f();\n    return 1;\n  endfunction\n"
             "endclass\nfunction void uf();\nendfunction\n"
             "module t;\n  initial begin\n    k::f();\n    uf();\n"
             "    void'(k::g());\n  end\nendmodule\n"));
}

TEST(VoidDataType, DISABLED_VoidAsTheTypeOfADeclarationIsReported) {
  struct Declaration {
    const char* src;
    const char* marker;
  };
  const Declaration kDeclarations[] = {
      {"module t;\n  void v;\nendmodule\n", "void v"},
      {"module t;\n  void a[2];\nendmodule\n", "void a"},
      {"module t;\n  function void f();\n    void l;\n  endfunction\n"
       "endmodule\n",
       "void l"},
      {"module t;\n  typedef void T;\nendmodule\n", "void T"},
      {"module t;\n  function int f(void x);\n    return 0;\n  endfunction\n"
       "endmodule\n",
       "void x"},
      {"module t;\n  task tk(output void o);\n  endtask\nendmodule\n",
       "void o"},
      {"module t #(parameter void P = 0);\nendmodule\n", "void P"},
      {"module t(input void x);\nendmodule\n", "void x"},
      {"module t(output void y);\nendmodule\n", "void y"},
      {"class C;\n  void p;\nendclass\nmodule t;\nendmodule\n", "void p"},
      {"package k;\n  void v;\nendpackage\nmodule t;\nendmodule\n", "void v"},
      {"void v;\nmodule t;\nendmodule\n", "void v"},
      {"interface i;\n  void v;\nendinterface\nmodule t;\n  i u();\n"
       "endmodule\n",
       "void v"},
  };
  for (const Declaration& d : kDeclarations) {
    SCOPED_TRACE(d.src);
    EXPECT_TRUE(ReportedOn(d.src, d.marker, "void", "6.13"));
  }
}

TEST(VoidDataType, VoidMemberOutsideATaggedUnionIsReported) {
  const char* const kSources[] = {
      "module t;\n  struct { void a; int b; } s;\nendmodule\n",
      "module t;\n  union { void a; int b; } s;\nendmodule\n",
      "module t;\n  struct packed { void a; logic b; } s;\nendmodule\n",
  };
  for (const char* src : kSources) {
    SCOPED_TRACE(src);
    EXPECT_TRUE(
        ReportedOn(src, "void a", "void member is only allowed", "7.2"));
  }
}

}  // namespace
