#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(BuiltinMethodElaboration, ArraySizeMethodElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int arr [];\n"
             "  int s;\n"
             "  initial s = arr.size();\n"
             "endmodule\n"));
}

TEST(BuiltinMethodElaboration, ArraySizeNoParensElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int arr [];\n"
             "  int s;\n"
             "  initial s = arr.size;\n"
             "endmodule\n"));
}

TEST(BuiltinMethodElaboration, QueuePushBackOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int q [$];\n"
             "  initial begin\n"
             "    q.push_back(42);\n"
             "  end\n"
             "endmodule\n"));
}

TEST(BuiltinMethodElaboration, DynArraySizeElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int dyn [];\n"
             "  int sz;\n"
             "  initial sz = dyn.size();\n"
             "endmodule\n"));
}

TEST(BuiltinMethodElaboration, StringLenOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  string s;\n"
             "  int n;\n"
             "  initial n = s.len();\n"
             "endmodule\n"));
}

TEST(BuiltinMethodElaboration, EnumNumOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  typedef enum {RED, GREEN, BLUE} color_e;\n"
             "  color_e c;\n"
             "  int n;\n"
             "  initial n = c.num();\n"
             "endmodule\n"));
}

TEST(BuiltinMethodElaboration, MethodWithDefaultArgNoParensOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  typedef enum {RED, GREEN, BLUE} color_e;\n"
             "  color_e c;\n"
             "  color_e n;\n"
             "  initial n = c.next;\n"
             "endmodule\n"));
}

TEST(BuiltinMethodElaboration, MethodNoParensInExpressionOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int arr [];\n"
             "  int r;\n"
             "  initial r = arr.size + 1;\n"
             "endmodule\n"));
}

TEST(BuiltinMethodElaboration, DynArraySizeNoParensElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int dyn [];\n"
             "  int sz;\n"
             "  initial sz = dyn.size;\n"
             "endmodule\n"));
}

TEST(BuiltinMethodElaboration, AssocNumNoParensElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int assoc [string];\n"
             "  int n;\n"
             "  initial n = assoc.num;\n"
             "endmodule\n"));
}

TEST(BuiltinMethodElaboration, StringLenNoParensElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  string s;\n"
             "  int n;\n"
             "  initial n = s.len;\n"
             "endmodule\n"));
}

TEST(BuiltinMethodElaboration, ImplicitVariableWithParenthesesIsAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int q[$] = {3, 1, 2, 1};\n"
      "  string s = \"ab\";\n"
      "  int x;\n"
      "  initial begin\n"
      "    x = q.min()[0];\n"
      "    x = s.toupper()[1];\n"
      "    x = q.unique().size();\n"
      "    x = q.unique().size;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(BuiltinMethodElaboration,
     DISABLED_ImplicitVariableWithoutParenthesesIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int q[$] = {3, 1, 2, 1};\n"
      "  string s = \"ab\";\n"
      "  int x;\n"
      "  initial begin\n"
      "    x = q.min[0];\n"
      "    x = s.toupper[1];\n"
      "    x = q.unique.size();\n"
      "  end\n"
      "endmodule\n",
      f);
  for (uint32_t line : {6u, 7u, 8u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "a built-in method call used as an implicit "
                              "variable shall include its parentheses",
                              line, "5.13"))
        << line;
  }
}

}  // namespace
