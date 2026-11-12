#include <gtest/gtest.h>

#include <cstddef>
#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

namespace {

TEST(JumpStatementElaboration, ReturnStringVariableFromIntFunctionIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function int h();\n"
      "    string s;\n"
      "    return s;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "return expression in function 'h' is not "
                            "assignment-compatible with the function's return "
                            "type",
                            4, "12.8"));
}

TEST(JumpStatementElaboration, ReturnClassHandleFromIntFunctionIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  class A; endclass\n"
      "  function int g(A a);\n"
      "    return a;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "return expression in function 'g' is not "
                            "assignment-compatible with the function's return "
                            "type",
                            4, "12.8"));
}

TEST(JumpStatementElaboration, ReturnIntegralValuesFromIntFunctionOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function int h(int k);\n"
      "    string s;\n"
      "    if (k > 0) return s.len();\n"
      "    return k;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(JumpStatementElaboration, ReturnUnrelatedHandleFromClassFunctionIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  class A; endclass\n"
      "  class B; endclass\n"
      "  function automatic A f();\n"
      "    B b = new;\n"
      "    return b;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "return expression in function 'f' is not "
                            "assignment-compatible with the function's return "
                            "type",
                            6, "12.8"));
}

TEST(JumpStatementElaboration, ReturnIntegerFromClassFunctionIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  class A; endclass\n"
      "  function A g();\n"
      "    return 5;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "return expression in function 'g' is not "
                            "assignment-compatible with the function's return "
                            "type",
                            4, "12.8"));
}

TEST(JumpStatementElaboration, ReturnFittingValuesFromNamedTypeFunctionsOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  class A; endclass\n"
      "  class D extends A; endclass\n"
      "  typedef int T;\n"
      "  function automatic A f(bit k);\n"
      "    D d = new;\n"
      "    if (k) return d;\n"
      "    return new;\n"
      "  endfunction\n"
      "  function T g();\n"
      "    return 1;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(JumpStatementElaboration, ReturnRealFromStringTypedefFunctionIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef string S;\n"
      "  function S g();\n"
      "    return 1.5;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "return expression in function 'g' is not "
                            "assignment-compatible with the function's return "
                            "type",
                            4, "12.8"));
}

TEST(JumpStatementElaboration, ReturnTypeNamedByAClassTypedefIsTheClasssType) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef enum {X, Y} t_t;\n"
      "  class K;\n"
      "    typedef string t_t;\n"
      "    function t_t gets(); return \"\"; endfunction\n"
      "  endclass\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(JumpStatementElaboration,
     ReturnOfANameANestedBlockHidesReadsTheBlocksType) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  class A; endclass\n"
      "  function automatic A f(int v);\n"
      "    begin\n"
      "      A v = new;\n"
      "      return v;\n"
      "    end\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(JumpStatementElaboration, ReturnOfAnIntANestedBlockDeclaresIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  class A; endclass\n"
      "  function automatic A f(A v);\n"
      "    begin\n"
      "      int v = 1;\n"
      "      return v;\n"
      "    end\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "return expression in function 'f' is not "
                            "assignment-compatible with the function's return "
                            "type",
                            6, "12.8"));
}

TEST(JumpStatementElaboration, ReturnOfAnArrayANestedBlockDeclaresElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  class A; endclass\n"
      "  typedef int pair_t[2];\n"
      "  function automatic pair_t f(A v);\n"
      "    begin\n"
      "      int v[2];\n"
      "      return v;\n"
      "    end\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(JumpStatementElaboration, ReturnOfANameAForLoopDeclaresReadsTheLoopsType) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  class A; endclass\n"
      "  function automatic A f(int v);\n"
      "    for (A v = null; v != null; ) return v;\n"
      "    for (v = 0; v < 2; v++) ;\n"
      "    return null;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(JumpStatementElaboration, ReturnOfAnIntAForLoopDeclaresIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  class A; endclass\n"
      "  function automatic A f(A v);\n"
      "    for (int v = 0; v < 2; v++) return v;\n"
      "    return null;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "return expression in function 'f' is not "
                            "assignment-compatible with the function's return "
                            "type",
                            4, "12.8"));
}

TEST(JumpStatementElaboration, ReturnOfAnIntIndexedForeachVariableIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  class A; endclass\n"
      "  int fx[4];\n"
      "  function automatic A f(A v);\n"
      "    int dyn[];\n"
      "    int q[$];\n"
      "    int grid[2][3];\n"
      "    bit [3:0] bits;\n"
      "    foreach (fx[v]) return v;\n"
      "    foreach (dyn[v]) return v;\n"
      "    foreach (q[v]) return v;\n"
      "    foreach (grid[, v]) return v;\n"
      "    foreach (bits[v]) return v;\n"
      "    return null;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  for (int line = 9; line <= 13; ++line) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "return expression in function 'f' is not "
                              "assignment-compatible with the function's "
                              "return type",
                              line, "12.8"))
        << line;
  }
}

TEST(JumpStatementElaboration, ForeachVariableOfAnUnreadDimensionHidesFormal) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  class A; endclass\n"
      "  class H; int arr[4]; endclass\n"
      "  typedef int row_t[4];\n"
      "  bit [3:0] mod_bits;\n"
      "  function automatic int f(A v, H h);\n"
      "    int by_key[byte];\n"
      "    row_t row;\n"
      "    foreach (by_key[v]) return v;\n"
      "    foreach (row[v]) return v;\n"
      "    foreach (h.arr[v]) return v;\n"
      "    foreach (mod_bits[v]) return v;\n"
      "    return 0;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(JumpStatementElaboration, ReturnOfAModuleVariableIsCheckedAgainstType) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  class A; endclass\n"
      "  int g;\n"
      "  function automatic A f();\n"
      "    return g;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "return expression in function 'f' is not "
                            "assignment-compatible with the function's return "
                            "type",
                            5, "12.8"));
}

TEST(JumpStatementElaboration, AFunctionsDeclarationHidesAModuleVariable) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  class A; endclass\n"
      "  int g;\n"
      "  function automatic A f();\n"
      "    A g = new;\n"
      "    return g;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(JumpStatementElaboration, ReturnOfAClassPropertyIsCheckedAgainstType) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  class A; endclass\n"
      "  class B;\n"
      "    int count;\n"
      "    function A get();\n"
      "      return count;\n"
      "    endfunction\n"
      "  endclass\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "return expression in function 'get' is not "
                            "assignment-compatible with the function's return "
                            "type",
                            6, "12.8"));
}

TEST(JumpStatementElaboration,
     ReturnOfAnInheritedPropertyIsCheckedAgainstType) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  class A; endclass\n"
      "  class P; int total; endclass\n"
      "  class D extends P;\n"
      "    function A first(); return total; endfunction\n"
      "  endclass\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "return expression in function 'first' is not "
                            "assignment-compatible with the function's return "
                            "type",
                            5, "12.8"));
}

TEST(JumpStatementElaboration,
     ReturnOfAPropertyFromAnOutOfBlockMethodIsChecked) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  class A; endclass\n"
      "  class C;\n"
      "    int size;\n"
      "    extern function A pick();\n"
      "  endclass\n"
      "  function A C::pick();\n"
      "    return size;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "return expression in function 'pick' is not "
                            "assignment-compatible with the function's return "
                            "type",
                            8, "12.8"));
}

TEST(JumpStatementElaboration, ReturnOfAPropertyFromAnEnumMethodIsChecked) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  class E;\n"
      "    int level;\n"
      "    function enum {LOW, HIGH} grade();\n"
      "      return level;\n"
      "    endfunction\n"
      "  endclass\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "return expression in function 'grade' is not "
                            "assignment-compatible with the function's return "
                            "type",
                            5, "12.8"));
}

TEST(JumpStatementElaboration, ANearerDeclarationHidesAClassProperty) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  class A; endclass\n"
      "  class P; int item; int slot; endclass\n"
      "  class D extends P;\n"
      "    A item;\n"
      "    function A own(); return item; endfunction\n"
      "    function A local_one();\n"
      "      A slot = new;\n"
      "      return slot;\n"
      "    endfunction\n"
      "  endclass\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(JumpStatementElaboration, ReturnOfAVariableAroundAClassIsChecked) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  class A; endclass\n"
      "  int g;\n"
      "  class B;\n"
      "    function A get();\n"
      "      return g;\n"
      "    endfunction\n"
      "  endclass\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "return expression in function 'get' is not "
                            "assignment-compatible with the function's return "
                            "type",
                            6, "12.8"));
}

TEST(JumpStatementElaboration, ReturnOfAUnitVariableFromAUnitClassIsChecked) {
  ElabFixture f;
  ElaborateSrc(
      "int g;\n"
      "class A; endclass\n"
      "class B;\n"
      "  function A get(); return g; endfunction\n"
      "endclass\n"
      "module m; endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "return expression in function 'get' is not "
                            "assignment-compatible with the function's return "
                            "type",
                            4, "12.8"));
}

TEST(JumpStatementElaboration,
     ReturnOfAnEnclosingClassPropertyFromANestedClassIsChecked) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  class A; endclass\n"
      "  class O;\n"
      "    static int depth;\n"
      "    class I;\n"
      "      function A get(); return depth; endfunction\n"
      "    endclass\n"
      "  endclass\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "return expression in function 'get' is not "
                            "assignment-compatible with the function's return "
                            "type",
                            6, "12.8"));
}

TEST(JumpStatementElaboration,
     ReturnOfAVariableAroundAClassFromAnOutOfBlockMethodIsChecked) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  class A; endclass\n"
      "  int g;\n"
      "  class C;\n"
      "    extern function A pick();\n"
      "  endclass\n"
      "  function A C::pick();\n"
      "    return g;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "return expression in function 'pick' is not "
                            "assignment-compatible with the function's return "
                            "type",
                            8, "12.8"));
}

TEST(JumpStatementElaboration, AClassDeclarationHidesAVariableAroundIt) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  class A; endclass\n"
      "  A p; A q; A e;\n"
      "  class B #(parameter int q = 1);\n"
      "    int p;\n"
      "    typedef enum {e, f} t;\n"
      "    function int one(); return p; endfunction\n"
      "    function int two(); return q; endfunction\n"
      "    function int three(); return e; endfunction\n"
      "  endclass\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(JumpStatementElaboration, AnUnknownBaseLeavesTheVariablesAroundUnread) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  class A; endclass\n"
      "  A g;\n"
      "  class P; int g; endclass\n"
      "  class B #(type T = P) extends T;\n"
      "    function int get(); return g; endfunction\n"
      "  endclass\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

struct JumpPlace {
  const char* head;
  const char* tail;
  int line;
};

constexpr JumpPlace kBlockPlaces[] = {
    {"module m;\n  initial begin\n    ", "\n  end\nendmodule\n", 3},
    {"module m;\n  int x;\n  always_comb begin\n    x = 0;\n    ",
     "\n  end\nendmodule\n", 5},
    {"module m;\n  final begin\n    ", "\n  end\nendmodule\n", 3},
    {"interface i;\n  initial begin\n    ",
     "\n  end\nendinterface\nmodule m;\n  i u();\nendmodule\n", 3},
    {"program p;\n  initial begin\n    ", "\n  end\nendprogram\n", 3}};

constexpr JumpPlace kGenerateBlockPlaces[] = {
    {"module m;\n  if (1) begin : g\n    initial begin\n      ",
     "\n    end\n  end\nendmodule\n", 4},
    {"module m;\n  for (genvar k = 0; k < 1; k++) begin : g\n    initial "
     "begin\n      ",
     "\n    end\n  end\nendmodule\n", 4},
    {"module m;\n  case (1)\n    1: begin : g\n      initial begin\n        ",
     "\n      end\n    end\n  endcase\nendmodule\n", 5}};

constexpr JumpPlace kSubroutinePlaces[] = {
    {"module m;\n  function void f();\n    ", "\n  endfunction\nendmodule\n",
     3},
    {"module m;\n  task t();\n    ", "\n  endtask\nendmodule\n", 3},
    {"class C;\n  function void f();\n    ", "\n  endfunction\nendclass\n", 3},
    {"class C;\n  task t();\n    ", "\n  endtask\nendclass\n", 3},
    {"package p;\n  function void f();\n    ", "\n  endfunction\nendpackage\n",
     3},
    {"program p;\n  function void f();\n    ", "\n  endfunction\nendprogram\n",
     3},
    {"function void f();\n  ", "\nendfunction\n", 2}};

constexpr JumpPlace kInterfaceSubroutinePlaces[] = {
    {"interface i;\n  task t();\n    ",
     "\n  endtask\nendinterface\nmodule m;\n  i u();\nendmodule\n", 3},
    {"interface i;\n  function void f();\n    ",
     "\n  endfunction\nendinterface\nmodule m;\n  i u();\nendmodule\n", 3}};

constexpr JumpPlace kValueFunctionPlaces[] = {
    {"module m;\n  function int f();\n    ", "\n  endfunction\nendmodule\n", 3},
    {"class C;\n  function int f();\n    ", "\n  endfunction\nendclass\n", 3},
    {"package p;\n  function int f();\n    ", "\n  endfunction\nendpackage\n",
     3},
    {"interface i;\n  function int f();\n    ",
     "\n  endfunction\nendinterface\nmodule m;\n  i u();\nendmodule\n", 3},
    {"program p;\n  function int f();\n    ", "\n  endfunction\nendprogram\n",
     3},
    {"function int f();\n  ", "\nendfunction\n", 2}};

struct LoopJump {
  const char* outside;
  const char* inside;
  const char* message;
};

constexpr LoopJump kLoopJumps[] = {
    {"break;", "for (int i = 0; i < 2; i++) break;",
     "break statement is not inside a loop"},
    {"continue;", "while (0) continue;",
     "continue statement is not inside a loop"}};

constexpr const char* kReturnOutside =
    "return statement is only allowed inside a subroutine";

constexpr const char* kNoValue = "gives no value to return";

std::string Placed(const JumpPlace& place, const char* stmt) {
  return std::string(place.head) + stmt + place.tail;
}

bool ElaboratesClean(const std::string& src) {
  ElabFixture f;
  ElaborateSrc(src, f);
  return !f.diag.HasErrors();
}

bool ElaborationReports(const std::string& src, const char* message, int line) {
  ElabFixture f;
  ElaborateSrc(src, f);
  return ReportedError(f.diag.Diagnostics(), message, line, "12.8");
}

template <std::size_t N>
void ExpectReportedIn(const JumpPlace (&places)[N], const char* stmt,
                      const char* message) {
  for (const auto& place : places) {
    EXPECT_TRUE(ElaborationReports(Placed(place, stmt), message, place.line))
        << Placed(place, stmt);
  }
}

template <std::size_t N>
void ExpectAcceptedIn(const JumpPlace (&places)[N], const char* stmt) {
  for (const auto& place : places) {
    EXPECT_TRUE(ElaboratesClean(Placed(place, stmt))) << Placed(place, stmt);
  }
}

TEST(JumpStatementElaboration,
     BreakAndContinueOutsideALoopAreReportedInEveryPlace) {
  for (const auto& jump : kLoopJumps) {
    ExpectReportedIn(kBlockPlaces, jump.outside, jump.message);
    ExpectReportedIn(kSubroutinePlaces, jump.outside, jump.message);
    ExpectReportedIn(kInterfaceSubroutinePlaces, jump.outside, jump.message);
  }
}

TEST(JumpStatementElaboration,
     DISABLED_BreakAndContinueOutsideALoopAreReportedInEveryGenerateBlock) {
  for (const auto& jump : kLoopJumps) {
    ExpectReportedIn(kGenerateBlockPlaces, jump.outside, jump.message);
  }
}

TEST(JumpStatementElaboration,
     BreakAndContinueInsideALoopAreAcceptedInEveryPlace) {
  for (const auto& jump : kLoopJumps) {
    ExpectAcceptedIn(kBlockPlaces, jump.inside);
    ExpectAcceptedIn(kGenerateBlockPlaces, jump.inside);
    ExpectAcceptedIn(kSubroutinePlaces, jump.inside);
    ExpectAcceptedIn(kInterfaceSubroutinePlaces, jump.inside);
  }
}

constexpr const char* kLoopHeads[] = {"for (int i = 0; i < 2; i++)",
                                      "repeat (2)", "while (x < 2)", "forever",
                                      "foreach (a[i])"};

constexpr const char* kJoins[] = {"join", "join_any", "join_none"};

std::string LoopAroundFork(const char* loop, const char* body,
                           const char* join) {
  return std::string(
             "module m;\n"
             "  int x;\n"
             "  int a [2];\n"
             "  initial begin\n"
             "    ") +
         loop +
         " begin\n"
         "      fork\n"
         "        " +
         body +
         "\n"
         "      " +
         join +
         "\n"
         "    end\n"
         "  end\n"
         "endmodule\n";
}

struct ForkJump {
  const char* stmt;
  const char* message;
};

constexpr ForkJump kForkJumps[] = {
    {"break;",
     "break inside fork-join cannot exit a loop outside the fork-join block"},
    {"continue;",
     "continue inside fork-join cannot affect a loop outside the fork-join "
     "block"},
    {"begin x++; break; end",
     "break inside fork-join cannot exit a loop outside the fork-join block"},
    {"if (x > 0) continue;",
     "continue inside fork-join cannot affect a loop outside the fork-join "
     "block"}};

TEST(JumpStatementElaboration,
     AJumpInAForkOutOfAnOuterLoopIsReportedInEveryForm) {
  for (const char* loop : kLoopHeads) {
    for (const char* join : kJoins) {
      for (const auto& jump : kForkJumps) {
        EXPECT_TRUE(ElaborationReports(LoopAroundFork(loop, jump.stmt, join),
                                       jump.message, 7))
            << loop << " " << jump.stmt << " " << join;
      }
    }
  }
}

TEST(JumpStatementElaboration, AJumpInALoopInsideAForkIsAcceptedInEveryForm) {
  for (const char* loop : kLoopHeads) {
    for (const char* join : kJoins) {
      for (const auto& jump : kForkJumps) {
        std::string inner = std::string("do ") + jump.stmt + " while (0);";
        EXPECT_TRUE(ElaboratesClean(LoopAroundFork(loop, inner.c_str(), join)))
            << loop << " " << jump.stmt << " " << join;
      }
    }
  }
}

TEST(JumpStatementElaboration,
     AReturnOutsideASubroutineIsReportedInEveryPlace) {
  ExpectReportedIn(kBlockPlaces, "return;", kReturnOutside);
}

TEST(JumpStatementElaboration,
     DISABLED_AReturnOutsideASubroutineIsReportedInEveryGenerateBlock) {
  ExpectReportedIn(kGenerateBlockPlaces, "return;", kReturnOutside);
}

TEST(JumpStatementElaboration, AReturnInsideASubroutineIsAcceptedInEveryPlace) {
  ExpectAcceptedIn(kSubroutinePlaces, "return;");
  ExpectAcceptedIn(kInterfaceSubroutinePlaces, "return;");
}

TEST(JumpStatementElaboration,
     ABareReturnFromAValuedFunctionIsReportedInEveryPlace) {
  ExpectReportedIn(kValueFunctionPlaces, "return;", kNoValue);
}

TEST(JumpStatementElaboration, AReturnWithAValueFromAValuedFunctionIsAccepted) {
  ExpectAcceptedIn(kValueFunctionPlaces, "return 1;");
}

}  // namespace
