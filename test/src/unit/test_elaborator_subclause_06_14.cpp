#include <gtest/gtest.h>

#include <initializer_list>
#include <string>
#include <string_view>

#include "elaborator/type_eval.h"
#include "fixture_elaborator.h"
#include "helpers_generate_block_items.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(ChandleDataType, ChandleWidth64) {
  DataType dt;
  dt.kind = DataTypeKind::kChandle;
  EXPECT_EQ(EvalTypeWidth(dt), 64u);
}

TEST(ChandleDataType, ChandleNotIntegral) {
  EXPECT_FALSE(IsIntegralType(DataTypeKind::kChandle));
}

TEST(ChandleDataType, ChandleNot4State) {
  EXPECT_FALSE(Is4stateType(DataTypeKind::kChandle));
}

TEST(ChandleDataType, ChandlePort_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top(input chandle ch);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "chandle cannot be used as a port type", 1,
                            "6.14"));
}

TEST(ChandleDataType, ChandleContAssign_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  chandle a, b;\n"
      "  assign a = b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "chandle cannot be used in continuous assignment",
                            3, "6.14"));
}

TEST(ChandleDataType, ChandleSensitivity_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  chandle ch;\n"
      "  always @(ch) begin end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "chandle cannot appear in event expression", 3,
                            "6.14"));
}

TEST(ChandleDataType, ChandleIsChandle) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  chandle ch;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->variables.empty());
  EXPECT_TRUE(mod->variables[0].is_chandle);
}

TEST(ChandleDataType, ChandleToChandleAssign_Ok) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  chandle a, b;\n"
      "  initial a = b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ChandleDataType, ChandleAssignNull_Ok) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  chandle h;\n"
      "  initial h = null;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ChandleDataType, ChandleOutputPort_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top(output chandle ch);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "chandle cannot be used as a port type", 1,
                            "6.14"));
}

TEST(ChandleDataType, ChandleInoutPort_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top(inout chandle ch);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "chandle cannot be used as a port type", 1,
                            "6.14"));
}

TEST(ChandleDataType, ChandleInUntaggedUnion_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  typedef union { chandle ch; int i; } my_union;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "chandle type can only be used in tagged unions", 2,
                            "7.3.2"));
}

TEST(ChandleDataType, ChandleInTaggedUnion_Ok) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  typedef union tagged { chandle Ch; int I; } my_union;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ChandleDataType, ChandleInsertedIntoAssociativeArray_Ok) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  chandle aa[int];\n"
      "  initial aa[3] = null;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ChandleDataType, ChandleAssociativeArrayElementRead_Ok) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  chandle aa[int];\n"
      "  chandle x;\n"
      "  initial x = aa[3];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ChandleDataType, ChandleAssociativeArrayElementWrite_Ok) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  chandle aa[int];\n"
      "  chandle x;\n"
      "  initial aa[3] = x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ChandleDataType, ChandleScalarBitSelect_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  chandle h;\n"
      "  chandle x;\n"
      "  initial x = h[0];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-select on chandle is illegal", 4, "6.14"));
}

TEST(ChandleDataType, ChandleInPackedStruct_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  typedef struct packed { chandle ch; int i; } my_struct;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "type of member 'ch' is not allowed in a packed structure", 2, "7.2.1"));
}

TEST(ChandleDataType, ChandleAssignToInt_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  chandle h;\n"
      "  int x;\n"
      "  initial x = h;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "chandle cannot be assigned to a non-chandle "
                            "variable",
                            4, "6.14"));
}

TEST(ChandleDataType, IntAssignToChandle_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  chandle h;\n"
      "  int x;\n"
      "  initial h = x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "chandle can only be assigned from another chandle "
                            "or null",
                            4, "6.14"));
}

TEST(ChandleDataType, ChandleAddition_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  chandle a, b;\n"
      "  int r;\n"
      "  initial r = a + b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "operator is not allowed on chandle", 4, "6.14"));
}

TEST(ChandleDataType, ChandleBitwiseOr_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  chandle a;\n"
      "  int r;\n"
      "  initial r = a | 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "operator is not allowed on chandle", 4, "6.14"));
}

TEST(ChandleDataType, ChandleUnaryNot_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  chandle h;\n"
      "  int r;\n"
      "  initial r = ~h;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "operator is not allowed on chandle", 4, "6.14"));
}

TEST(ChandleDataType, ChandleRelational_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  chandle a, b;\n"
      "  int r;\n"
      "  initial r = (a < b) ? 1 : 0;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "operator is not allowed on chandle", 4, "6.14"));
}

TEST(ChandleDataType, ChandleEqualityOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  chandle a, b;\n"
      "  int r;\n"
      "  initial r = (a == b) ? 1 : 0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ChandleDataType, ChandleInequalityOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  chandle h;\n"
      "  int r;\n"
      "  initial r = (h != null) ? 1 : 0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ChandleDataType, ChandleCaseEqualityOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  chandle h;\n"
      "  int r;\n"
      "  initial r = (h === null) ? 1 : 0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ChandleDataType, ChandleCaseInequalityOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  chandle h;\n"
      "  int r;\n"
      "  initial r = (h !== null) ? 1 : 0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ChandleDataType, ChandleAdditionInForkArm_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  chandle a, b;\n"
      "  int r;\n"
      "  initial fork\n"
      "    r = a + b;\n"
      "  join\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "operator is not allowed on chandle", 5, "6.14"));
}

TEST(ChandleDataType, ChandleAdditionInForInitialization_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  chandle a, b;\n"
      "  int r;\n"
      "  initial for (r = a + b; r < 1; r = r + 1) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "operator is not allowed on chandle", 4, "6.14"));
}

TEST(ChandleDataType, ChandleAdditionInForStep_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  chandle a, b;\n"
      "  int r;\n"
      "  initial for (r = 0; r < 1; r = a + b) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "operator is not allowed on chandle", 4, "6.14"));
}

TEST(ChandleDataType, ChandleAdditionInAssertionPassStatement_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  chandle a, b;\n"
      "  int r;\n"
      "  initial assert (1) r = a + b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "operator is not allowed on chandle", 4, "6.14"));
}

TEST(ChandleDataType, ChandleAdditionInAssertionFailStatement_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  chandle a, b;\n"
      "  int r;\n"
      "  initial assert (1) else r = a + b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "operator is not allowed on chandle", 4, "6.14"));
}

TEST(ChandleDataType, ChandleAdditionInRandcaseItem_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  chandle a, b;\n"
      "  int r;\n"
      "  initial randcase\n"
      "    1 : r = a + b;\n"
      "  endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "operator is not allowed on chandle", 5, "6.14"));
}

TEST(ChandleDataType, ChandleAdditionInRandsequenceCodeBlock_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  chandle a, b;\n"
      "  int r;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { r = a + b; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "operator is not allowed on chandle", 6, "6.14"));
}

TEST(ChandleDataType, ChandleAssignedFromAnImportedFunctionResult_Ok) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  import \"DPI-C\" function chandle give();\n"
      "  chandle keep;\n"
      "  initial keep = give();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "chandle can only be assigned from another "
                             "chandle or null",
                             4, "6.14"));
}

TEST(ChandleDataType, ChandleAssignedFromANativeFunctionResult_Ok) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  chandle keep;\n"
      "  function chandle mk();\n"
      "    return null;\n"
      "  endfunction\n"
      "  initial keep = mk();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "chandle can only be assigned from another "
                             "chandle or null",
                             6, "6.14"));
}

TEST(ChandleDataType, ImportedFunctionChandleResultAssignedToInt_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  import \"DPI-C\" function chandle give();\n"
      "  chandle keep;\n"
      "  int r;\n"
      "  initial r = give();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "chandle cannot be assigned to a non-chandle "
                            "variable",
                            5, "6.14"));
}

TEST(ChandleDataType, ChandleInsideGenerateBlocksIsRejected) {
  EXPECT_TRUE(RejectedInsideGenerateBlocks(
      {"", "chandle c; wire w;", "assign w = c;"},
      "chandle cannot be used in continuous assignment", "6.14"));
  EXPECT_TRUE(RejectedInsideGenerateBlocks(
      {"", "chandle c; logic y;", "always @(c) y = 0;"},
      "chandle cannot appear in event expression", "6.14"));
  EXPECT_TRUE(AcceptedInsideGenerateBlocks(
      {"", "chandle c; logic y;", "always @(c == null) y = 0;"}));
}

::testing::AssertionResult ReportedOn(const std::string& src,
                                      std::string_view marker,
                                      std::string_view message,
                                      std::string_view subclause = "6.14") {
  ElabFixture f;
  ElaborateSrc(src, f);
  return ReportedError(f.diag.Diagnostics(), message, LineHolding(src, marker),
                       subclause);
}

constexpr std::string_view kOperator = "operator is not allowed on chandle";
constexpr std::string_view kFromOther =
    "chandle can only be assigned from another chandle or null";
constexpr std::string_view kToOther =
    "chandle cannot be assigned to a non-chandle variable";
constexpr std::string_view kPort = "chandle cannot be used as a port type";
constexpr std::string_view kEvent = "chandle cannot appear in event expression";
constexpr std::string_view kUntagged =
    "chandle type can only be used in tagged unions";

std::string InModule(std::string_view items) {
  return std::string(
             "module t;\n  chandle h, g;\n  int r;\n  logic x, y, en;\n"
             "  string s;\n  real q;\n  logic [63:0] v;\n  event e;\n"
             "  class C;\n  endclass\n  C c;\n")
      .append(items)
      .append("\nendmodule\n");
}

void ExpectEachReported(std::initializer_list<const char*> items,
                        std::string_view message) {
  for (const char* item : items) {
    SCOPED_TRACE(item);
    EXPECT_TRUE(ReportedOn(InModule(item), item, message));
  }
}

TEST(ChandleDataType, EveryOtherOperatorOnAChandleIsReported) {
  ExpectEachReported(
      {"initial r = !h;", "initial r = h && x;", "initial r = h || x;",
       "initial r = -h;", "initial r = h << 1;", "initial h++;"},
      kOperator);
}

TEST(ChandleDataType,
     DISABLED_ConcatenationComparisonWithAnIntAndInsideAreReported) {
  ExpectEachReported({"initial v = {h};", "initial r = h == 0;",
                      "initial r = h inside {null};"},
                     kOperator);
}

TEST(ChandleDataType, BooleanTestsAndComparisonsOfChandlesAreAccepted) {
  EXPECT_TRUE(
      ElabOk(InModule("initial begin\n    r = h ? 1 : 0;\n    r = h != g;\n"
                      "    r = h === null;\n    while (h) h = null;\n"
                      "    do h = g; while (h);\n    for (; h; ) h = null;\n"
                      "    if (!(h == null)) r = 1;\n  end")));
}

TEST(ChandleDataType, AChandleAssignedToAStringRealVectorIsReported) {
  ExpectEachReported({"initial s = h;", "initial q = h;", "initial v = h;"},
                     kToOther);
}

TEST(ChandleDataType, AChandleAssignedToAClassVariableOrAnIntIsReported) {
  EXPECT_TRUE(ReportedOn(InModule("initial c = h;"), "c = h", kToOther));
  EXPECT_TRUE(ReportedOn(InModule("initial h = 0;"), "h = 0", kFromOther));
  EXPECT_TRUE(ReportedOn(InModule("initial h = c;"), "h = c",
                         "cannot assign class object handle", "8.4"));
}

TEST(ChandleDataType, AStringOrEventAssignedToAChandleIsReported) {
  ExpectEachReported({"initial h = s;", "initial h = e;"}, kFromOther);
}

std::string WithSubroutines(std::string_view use) {
  return std::string(
             "module t;\n  chandle h;\n  int r;\n"
             "  function int fi(int a);\n    return a;\n  endfunction\n"
             "  function void fc(chandle a);\n  endfunction\n"
             "  task automatic to(output chandle o);\n    o = null;\n"
             "  endtask\n  initial ")
      .append(use)
      .append("\nendmodule\n");
}

TEST(ChandleDataType, DISABLED_AChandleBoundToAnIntFormalOrActualIsReported) {
  EXPECT_TRUE(ReportedOn(WithSubroutines("r = fi(h);"), "fi(h)", kToOther));
  EXPECT_TRUE(ReportedOn(WithSubroutines("fc(r);"), "fc(r)", kFromOther));
  EXPECT_TRUE(ReportedOn(WithSubroutines("to(r);"), "to(r)", kToOther));
}

TEST(ChandleDataType, AChandleBoundToChandleFormalsAndActualsIsAccepted) {
  EXPECT_TRUE(ElabOk(WithSubroutines(
      "begin\n    fc(h);\n    fc(null);\n    to(h);\n    r = fi(r);\n"
      "  end")));
}

TEST(ChandleDataType, AChandleReturnedAsAnIntOrAnIntAsAChandleIsReported) {
  EXPECT_TRUE(ReportedOn(
      "module t;\n  chandle h;\n  function int rc();\n    return h;\n"
      "  endfunction\nendmodule\n",
      "return h", "not assignment-compatible", "12.8"));
  EXPECT_TRUE(
      ReportedOn("module t;\n  function chandle ri();\n    return 5;\n"
                 "  endfunction\nendmodule\n",
                 "return 5", "not assignment-compatible", "12.8"));
}

TEST(ChandleDataType,
     OperatorOnAChandleInAnInterfaceProgramOrCheckerIsReported) {
  EXPECT_TRUE(
      ReportedOn("interface i;\n  chandle h;\n  int r;\n  initial r = h + 1;\n"
                 "endinterface\nmodule t;\n  i u();\nendmodule\n",
                 "h + 1", kOperator));
  EXPECT_TRUE(
      ReportedOn("program p;\n  chandle h;\n  int r;\n  initial r = h + 1;\n"
                 "endprogram\nmodule t;\n  p u();\nendmodule\n",
                 "h + 1", kOperator));
  EXPECT_TRUE(
      ReportedOn("checker c(logic clk);\n  chandle h;\n  int r;\n"
                 "  always_comb r = h + 1;\nendchecker\n"
                 "module t;\n  logic clk;\n  c u(clk);\nendmodule\n",
                 "h + 1", kOperator));
}

TEST(ChandleDataType,
     DISABLED_OperatorOnAChandleInAClassPackageOrUnitIsReported) {
  EXPECT_TRUE(ReportedOn(
      "class C;\n  chandle h;\n  function int f();\n    return h + 1;\n"
      "  endfunction\nendclass\nmodule t;\nendmodule\n",
      "h + 1", kOperator));
  EXPECT_TRUE(ReportedOn(
      "package k;\n  chandle h;\n  function int f();\n    return h + 1;\n"
      "  endfunction\nendpackage\nmodule t;\nendmodule\n",
      "h + 1", kOperator));
  EXPECT_TRUE(
      ReportedOn("chandle h;\nfunction int f();\n  return h + 1;\nendfunction\n"
                 "module t;\nendmodule\n",
                 "h + 1", kOperator));
}

TEST(ChandleDataType, ChandleComparisonsInAClassPackageOrUnitAreAccepted) {
  EXPECT_TRUE(
      ElabOk("class C;\n  chandle h;\n  function int f();\n"
             "    return h == null;\n  endfunction\nendclass\npackage k;\n"
             "  chandle h;\n  function int f();\n    return h != null;\n"
             "  endfunction\nendpackage\nchandle h;\nfunction int f();\n"
             "  return h ? 1 : 0;\nendfunction\nmodule t;\nendmodule\n"));
}

TEST(ChandleDataType, RefNonAnsiProgramAndArrayPortsOfChandleAreReported) {
  EXPECT_TRUE(
      ReportedOn("module m(ref chandle ch);\nendmodule\n", "ref", kPort));
  EXPECT_TRUE(ReportedOn("module m(ch);\n  input chandle ch;\nendmodule\n",
                         "m(ch)", kPort));
  EXPECT_TRUE(
      ReportedOn("program p(input chandle ch);\nendprogram\n", "input", kPort));
  EXPECT_TRUE(ReportedOn("module m(input chandle chs [2]);\nendmodule\n",
                         "input", kPort));
}

TEST(
    ChandleDataType,
    DISABLED_TypedefInterfaceCheckerStructAndModportPortsOfChandleAreReported) {
  EXPECT_TRUE(ReportedOn(
      "typedef chandle h_t;\nmodule m(input var h_t ch);\nendmodule\n",
      "h_t ch", kPort));
  EXPECT_TRUE(ReportedOn("interface i(input chandle ch);\nendinterface\n",
                         "input", kPort));
  EXPECT_TRUE(
      ReportedOn("checker c(chandle ch);\nendchecker\n", "chandle ch", kPort));
  EXPECT_TRUE(
      ReportedOn("typedef struct { chandle h; } S;\nmodule m(input var S s);\n"
                 "endmodule\n",
                 "S s", kPort));
  EXPECT_TRUE(
      ReportedOn("interface i;\n  chandle ch;\n  modport mp(input ch);\n"
                 "endinterface\nmodule t;\nendmodule\n",
                 "modport", kPort));
}

TEST(ChandleDataType, ChandleArgumentsOfTasksFunctionsAndMethodsAreAccepted) {
  EXPECT_TRUE(
      ElabOk("class C;\n  function void f(chandle a);\n  endfunction\n"
             "endclass\nmodule t;\n"
             "  task automatic tk(input chandle a, output chandle b,\n"
             "                    ref chandle c);\n    b = a;\n  endtask\n"
             "  function chandle f(chandle a);\n    return a;\n"
             "  endfunction\nendmodule\n"));
}

TEST(ChandleDataType, ChandleInPackedOrUntaggedUnionsInEveryPlaceIsReported) {
  EXPECT_TRUE(
      ReportedOn("module t;\n  union tagged packed { chandle ch; int i; } u;\n"
                 "endmodule\n",
                 "chandle ch", "not allowed in a packed union", "7.2.1"));
  EXPECT_TRUE(
      ReportedOn("module t;\n  union packed { chandle ch; } u;\nendmodule\n",
                 "chandle ch", kUntagged, "7.3.2"));
  EXPECT_TRUE(ReportedOn(
      "module t;\n  typedef chandle h_t;\n  union { h_t h; int i; } u;\n"
      "endmodule\n",
      "h_t h", kUntagged, "7.3.2"));
  EXPECT_TRUE(
      ReportedOn("class C;\n  union { chandle h; int i; } u;\nendclass\n"
                 "module t;\nendmodule\n",
                 "chandle h", kUntagged, "7.3.2"));
  EXPECT_TRUE(
      ReportedOn("package k;\n  struct packed { chandle h; } p;\nendpackage\n"
                 "module t;\nendmodule\n",
                 "chandle h", "not allowed in a packed structure", "7.2.1"));
  EXPECT_TRUE(
      ReportedOn("union { chandle h; int i; } u;\nmodule t;\nendmodule\n",
                 "chandle h", kUntagged, "7.3.2"));
}

TEST(ChandleDataType,
     DISABLED_ChandleNestedInAStructInsideAnUntaggedUnionIsReported) {
  EXPECT_TRUE(
      ReportedOn("module t;\n  typedef struct { chandle h; } s_t;\n"
                 "  union { s_t s; int i; } u;\nendmodule\n",
                 "s_t s;", kUntagged, "7.3.2"));
}

TEST(ChandleDataType, ChandleInUnpackedStructsArraysAndTaggedUnionsIsAccepted) {
  EXPECT_TRUE(
      ElabOk("module t;\n  struct { chandle h; int i; } s;\n"
             "  chandle a[2];\n  chandle q[$];\n"
             "  union tagged { chandle h; int i; } tu;\nendmodule\n"));
}

TEST(ChandleDataType, ChandleInEveryAlwaysEventExpressionIsReported) {
  ExpectEachReported(
      {"always @(posedge h) y = 0;", "always @(negedge h) y = 0;",
       "always @(edge h) y = 0;", "always @(h or x) y = 0;",
       "always @(x, h) y = 0;", "always @(h iff en) y = 0;",
       "always_ff @(posedge h) y <= 0;"},
      kEvent);
}

TEST(ChandleDataType,
     DISABLED_ChandleInProceduralClockingAndAssertionEventsIsReported) {
  ExpectEachReported(
      {"initial @(h);", "task tk;\n    @(h);\n  endtask",
       "function void f;\n    fork @(h); join_none\n  endfunction",
       "initial y = @(h) 1;", "clocking cb @(h); endclocking",
       "a1: assert property (@(h) x);"},
      kEvent);
}

TEST(ChandleDataType, EventsOnAnEventOrAChandleComparisonAreAccepted) {
  EXPECT_TRUE(ElabOk(InModule(
      "initial @(e);\n  always @(h == null) y = 0;\n"
      "  initial wait (h != null);\n  clocking cb @(posedge x); endclocking")));
}

TEST(ChandleDataType, ChandleInAnInterfaceEventExpressionIsReported) {
  EXPECT_TRUE(ReportedOn(
      "interface i;\n  chandle h;\n  logic y;\n  always @(h) y = 0;\n"
      "endinterface\nmodule t;\n  i u();\nendmodule\n",
      "@(h)", kEvent));
}

TEST(ChandleDataType,
     DISABLED_ChandleInAClassPackageUnitOrProgramEventIsReported) {
  EXPECT_TRUE(
      ReportedOn("class C;\n  chandle h;\n  task tk();\n    @(h);\n  endtask\n"
                 "endclass\nmodule t;\nendmodule\n",
                 "@(h)", kEvent));
  EXPECT_TRUE(
      ReportedOn("package k;\n  chandle h;\n  task automatic tk();\n    @(h);\n"
                 "  endtask\nendpackage\nmodule t;\nendmodule\n",
                 "@(h)", kEvent));
  EXPECT_TRUE(
      ReportedOn("chandle h;\ntask automatic tk();\n  @(h);\nendtask\n"
                 "module t;\nendmodule\n",
                 "@(h)", kEvent));
  EXPECT_TRUE(
      ReportedOn("program p;\n  chandle h;\n  initial @(h);\nendprogram\n"
                 "module t;\n  p u();\nendmodule\n",
                 "@(h)", kEvent));
}

std::string WithChandleHolders(std::string_view use) {
  return std::string(
             "package k;\n  chandle ph;\n  typedef struct { chandle h; } PS;\n"
             "  PS ps;\nendpackage\n"
             "class C;\n  chandle h;\n  static chandle sh;\n"
             "  function void set(chandle x);\n    h = x;\n    this.h = x;\n"
             "  endfunction\nendclass\n"
             "interface ifc;\n  chandle h;\nendinterface\n"
             "module t;\n  typedef struct { chandle h; int k; } S;\n"
             "  chandle b;\n  C c = new;\n  S s, sa[2];\n  ifc i();\n"
             "  chandle arr[2];\n  if (1) begin : g\n    chandle h;\n  end\n"
             "  initial ")
      .append(use)
      .append("\nendmodule\n");
}

TEST(ChandleDataType,
     DISABLED_AChandleWrittenToOrReadFromADottedNameIsAccepted) {
  const char* const kUses[] = {
      "c.h = b;",   "s.h = b;",     "sa[1].h = b;", "C::sh = b;", "i.h = b;",
      "k::ph = b;", "k::ps.h = b;", "g.h = b;",     "b = c.h;",   "b = s.h;",
  };
  for (const char* use : kUses) {
    SCOPED_TRACE(use);
    EXPECT_TRUE(ElabOk(WithChandleHolders(use)));
  }
}

TEST(ChandleDataType, AChandleWrittenThroughAMethodPatternOrElementIsAccepted) {
  EXPECT_TRUE(ElabOk(WithChandleHolders(
      "begin\n    c.set(b);\n    s = '{h: b, k: 0};\n    arr[1] = b;\n"
      "    c.h = null;\n    s.h = null;\n  end")));
}

TEST(ChandleDataType,
     DISABLED_AnIntWrittenToAChandleMemberOrPropertyIsReported) {
  EXPECT_TRUE(
      ReportedOn(WithChandleHolders("c.h = 5;"), "c.h = 5", kFromOther));
  EXPECT_TRUE(
      ReportedOn(WithChandleHolders("s.h = 5;"), "s.h = 5", kFromOther));
}

TEST(ChandleDataType, AlwaysCombAndAlwaysLatchComparingAChandleAreAccepted) {
  EXPECT_TRUE(
      ElabOk(InModule("always_comb r = (h == null);\n  always_latch if (en) x "
                      "= (h != null);")));
}

}  // namespace
