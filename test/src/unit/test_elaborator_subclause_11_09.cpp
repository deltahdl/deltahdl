#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// §11.9 takes a tagged expression's type from its context, which shall be a
// tagged union: an int, a module's or a block's, has no member to name.
TEST(ExpressionElaboration, TaggedExpressionAssignedToIntReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int y;\n"
      "  initial begin\n"
      "    automatic int x;\n"
      "    x = tagged Valid 42;\n"
      "    y = tagged Valid 42;\n"
      "  end\n"
      "endmodule\n",
      f);
  for (uint32_t line : {5u, 6u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "tagged union expression in a context whose "
                              "type is not a tagged union",
                              line, "11.9"));
  }
  EXPECT_EQ(f.diag.ErrorCount(), 2u);
}

TEST(ExpressionElaboration, TaggedUnionVoidMemberElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef union tagged { void Invalid; int Valid; } VInt;\n"
      "  VInt u;\n"
      "  initial begin\n"
      "    u = tagged Invalid;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ExpressionElaboration, TaggedUnionMemberAccessElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef union tagged { int A; int B; } U;\n"
      "  U u;\n"
      "  int result;\n"
      "  initial begin\n"
      "    u = tagged A 10;\n"
      "    result = u.A;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// When the LHS variable is a tagged union typedef, the tag name in a tagged
// expression must be one of the declared members; otherwise the elaborator
// rejects the assignment.
TEST(ExpressionElaboration, TaggedUnionUnknownMemberRejected) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef union tagged { int A; int B; } U;\n"
      "  U u;\n"
      "  initial begin\n"
      "    u = tagged Bogus 7;\n"
      "  end\n"
      "endmodule\n",
      f);
  (void)design;
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "tagged union 'U' has no member named 'Bogus'", 5,
                            "11.9"));
}

// §11.9: the member-name rule also governs a declaration initializer, whose
// tagged expression type is known from the declared variable. A tag that is a
// declared member is accepted.
TEST(ExpressionElaboration, TaggedUnionInitializerKnownMemberAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef union tagged { int A; int B; } U;\n"
      "  U u = tagged A 7;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// The same rule rejects a declaration initializer whose tag is not a member of
// the declared tagged union type.
TEST(ExpressionElaboration, TaggedUnionInitializerUnknownMemberRejected) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef union tagged { int A; int B; } U;\n"
      "  U u = tagged Bogus 7;\n"
      "endmodule\n",
      f);
  (void)design;
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "tagged union 'U' has no member named 'Bogus'", 3,
                            "11.9"));
}

TEST(ExpressionElaboration, NestedTaggedUnionElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef union tagged {\n"
      "    int A;\n"
      "    int B;\n"
      "  } Inner;\n"
      "  typedef union tagged {\n"
      "    Inner X;\n"
      "    int Y;\n"
      "  } Outer;\n"
      "  Outer o;\n"
      "  initial begin\n"
      "    o = tagged X (tagged A 5);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §11.9 knows a tagged expression's type wherever its context gives one: a
// cast's type, either arm of a conditional, a continuous assignment's target,
// the return type of a function and the formal an argument binds to.
TEST(ExpressionElaboration, TaggedMemberNameCheckedInEveryContext) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef union tagged { void Invalid; int Valid; } VInt;\n"
      "  VInt u, v;\n"
      "  bit c;\n"
      "  initial u = VInt'(tagged Bogus 1);\n"
      "  initial u = c ? tagged Bogus 1 : tagged Invalid;\n"
      "  assign v = tagged Bogus 2;\n"
      "  function VInt f(); return tagged Bogus 3; endfunction\n"
      "  function void g(VInt a, int b[2]); endfunction\n"
      "  initial g(tagged Bogus 4, '{1, 2});\n"
      "  function void h(VInt a, VInt b = tagged Invalid); endfunction\n"
      "  initial h(.a(tagged Bogus 5));\n"
      "endmodule\n",
      f);
  for (uint32_t line : {5u, 6u, 7u, 8u, 10u, 12u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "tagged union 'VInt' has no member named 'Bogus'",
                              line, "11.9"));
  }
  EXPECT_EQ(f.diag.ErrorCount(), 6u);
}

// §11.9: the member's value shall have the member's type, which a literal
// does not give an unpacked structure; an assignment pattern does. A void
// member takes no value at all.
TEST(ExpressionElaboration, TaggedMemberValueCheckedAgainstMemberType) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef struct { int a, b; } pair_t;\n"
      "  typedef union tagged { void None; pair_t Add; int I; } U;\n"
      "  U u;\n"
      "  initial u = tagged Add 5;\n"
      "  initial u = tagged Add '{1, 2};\n"
      "  initial u = tagged None 1;\n"
      "  initial u = tagged I 7;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "value of tagged member 'Add' is not assignment "
                            "compatible with its type",
                            5, "11.9"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "void member 'None' of a tagged union takes no "
                            "value",
                            7, "11.9"));
  EXPECT_EQ(f.diag.ErrorCount(), 2u);
}

// A member written with an inline structure type gives its value that type,
// and a member that is itself a tagged union gives a tagged value its context.
// A union written inline in the declaration is named by no typedef.
TEST(ExpressionElaboration, InlineAndNestedTaggedUnionTypesChecked) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef union tagged { int A; int B; } Inner;\n"
      "  typedef union tagged {\n"
      "    struct { int p; } S;\n"
      "    Inner X;\n"
      "    int Arr [2];\n"
      "  } Outer;\n"
      "  Outer o;\n"
      "  union tagged { void A; int B; } w;\n"
      "  initial o = tagged S 1;\n"
      "  initial o = tagged X (tagged Bogus 5);\n"
      "  initial o = tagged Arr '{1, 2};\n"
      "  initial w = tagged C 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "value of tagged member 'S' is not assignment "
                            "compatible with its type",
                            10, "11.9"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "tagged union 'Inner' has no member named 'Bogus'",
                            11, "11.9"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "tagged union has no member named 'C'", 13,
                            "11.9"));
  EXPECT_EQ(f.diag.ErrorCount(), 3u);
}

// An untagged union is no tagged union, so its members are not named by
// `tagged` either (§7.3.2).
TEST(ExpressionElaboration, TaggedExpressionAssignedToUntaggedUnionReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef union { int a; real r; } UU;\n"
      "  UU w;\n"
      "  initial w = tagged a 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "tagged union expression in a context whose type "
                            "is not a tagged union",
                            4, "11.9"));
}

// A context whose type the elaborator does not know here -- an element or a
// select of a variable, an array, a port, a type reference, a class, a cast to
// a type no typedef names, and the formal of a method or of the compilation
// unit's function, which the module's own `f` does not declare -- gives a
// tagged expression nothing to be checked against, so none of these draws a
// §11.9 report.
TEST(ExpressionElaboration, TaggedExpressionInUnknownContextNotJudged) {
  ElabFixture f;
  ElaborateSrc(
      "typedef union tagged { int A; } U;\n"
      "function automatic int f(U a); return 0; endfunction\n"
      "module m(output int o);\n"
      "  class C; function void f(U a); endfunction endclass\n"
      "  function automatic int f(int a); return a; endfunction\n"
      "  U arr [2];\n"
      "  C h;\n"
      "  int i;\n"
      "  var type(i) tv;\n"
      "  int n = int'(4);\n"
      "  int k = 4'(i);\n"
      "  initial arr[0] = tagged Bogus 1;\n"
      "  initial arr = '{tagged Bogus 1, tagged A 2};\n"
      "  initial o = tagged Bogus 1;\n"
      "  initial tv = tagged Bogus 1;\n"
      "  initial h = tagged Bogus 1;\n"
      "  initial h.f(tagged A 1);\n"
      "  initial i = $unit::f(tagged A 1);\n"
      "endmodule\n",
      f);
  for (const auto& d : f.diag.Diagnostics()) {
    EXPECT_EQ(d.message.find("tagged union"), std::string::npos) << d.message;
  }
}

}  // namespace
