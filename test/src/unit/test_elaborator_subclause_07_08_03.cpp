#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(ClassIndexAssocArrayElaboration, AssocArrayClassIndex_IsAssoc) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  class Foo;\n"
      "    int id;\n"
      "  endclass\n"
      "  int data[Foo];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto& vars = design->top_modules[0]->variables;
  bool found = false;
  for (auto& v : vars) {
    if (v.name == "data") {
      EXPECT_TRUE(v.is_assoc);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(ClassIndexAssocArrayElaboration, AssocArrayClassIndex_IsClassIndex) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  class Bar;\n"
      "    int x;\n"
      "  endclass\n"
      "  int aa[Bar];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto& vars = design->top_modules[0]->variables;
  bool found = false;
  for (auto& v : vars) {
    if (v.name == "aa") {
      EXPECT_TRUE(v.is_class_index);
      EXPECT_EQ(v.assoc_index_class_name, "Bar");
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(ClassIndexAssocArrayElaboration, AssocArrayClassIndex_IndexWidth64) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  class MyKey;\n"
      "    int id;\n"
      "  endclass\n"
      "  int data[MyKey];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto& vars = design->top_modules[0]->variables;
  bool found = false;
  for (auto& v : vars) {
    if (v.name == "data") {
      EXPECT_EQ(v.assoc_index_width, 64u);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(ClassIndexAssocArrayElaboration, AssocArrayClassIndex_NotStringIndex) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  class C;\n"
      "    int x;\n"
      "  endclass\n"
      "  int aa[C];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto& vars = design->top_modules[0]->variables;
  bool found = false;
  for (auto& v : vars) {
    if (v.name == "aa") {
      EXPECT_FALSE(v.is_string_index);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(ClassIndexAssocArrayElaboration,
     AssocArrayClassIndex_LiteralIndexIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  class Foo;\n"
      "    int id;\n"
      "  endclass\n"
      "  int data[Foo];\n"
      "  initial data[7] = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "class-indexed associative array 'data' shall be "
                            "indexed by an object of class 'Foo'",
                            6, "7.8.3"));
}

TEST(ClassIndexAssocArrayElaboration,
     AssocArrayClassIndex_WrongClassHandleIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  class Foo;\n"
      "    int id;\n"
      "  endclass\n"
      "  class Bar;\n"
      "    int x;\n"
      "  endclass\n"
      "  Bar b;\n"
      "  int data[Foo];\n"
      "  initial data[b] = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "class-indexed associative array 'data' shall be "
                            "indexed by an object of class 'Foo'",
                            10, "7.8.3"));
}

TEST(ClassIndexAssocArrayElaboration,
     AssocArrayClassIndex_MatchingHandleNoError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  class Foo;\n"
      "    int id;\n"
      "  endclass\n"
      "  Foo k;\n"
      "  int data[Foo];\n"
      "  initial data[k] = 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ClassIndexAssocArrayElaboration, AssocArrayClassIndex_NullIndexNoError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  class Foo;\n"
      "    int id;\n"
      "  endclass\n"
      "  int data[Foo];\n"
      "  initial data[null] = 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ClassIndexAssocArrayElaboration,
     AssocArrayClassIndex_IntVariableIndexIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  class Foo;\n"
      "    int id;\n"
      "  endclass\n"
      "  int i;\n"
      "  int data[Foo];\n"
      "  initial data[i] = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "class-indexed associative array 'data' shall be "
                            "indexed by an object of class 'Foo'",
                            7, "7.8.3"));
}

TEST(ClassIndexAssocArrayElaboration,
     AssocArrayClassIndex_StringVariableIndexIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  class Foo;\n"
      "    int id;\n"
      "  endclass\n"
      "  string s;\n"
      "  int data[Foo];\n"
      "  initial data[s] = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "class-indexed associative array 'data' shall be "
                            "indexed by an object of class 'Foo'",
                            7, "7.8.3"));
}

TEST(ClassIndexAssocArrayElaboration,
     AssocArrayClassIndex_DerivedHandleNoError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  class Base;\n"
      "    int id;\n"
      "  endclass\n"
      "  class Derived extends Base;\n"
      "    int extra;\n"
      "  endclass\n"
      "  Derived d;\n"
      "  int data[Base];\n"
      "  initial data[d] = 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ClassIndexAssocArrayElaboration,
     AssocArrayClassIndex_BaseHandleForDerivedIndexIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  class Base;\n"
      "    int id;\n"
      "  endclass\n"
      "  class Derived extends Base;\n"
      "    int extra;\n"
      "  endclass\n"
      "  Base b;\n"
      "  int data[Derived];\n"
      "  initial data[b] = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "class-indexed associative array 'data' shall be "
                            "indexed by an object of class 'Derived'",
                            10, "7.8.3"));
}

TEST(ClassIndexAssocArrayElaboration,
     AssocArrayClassIndex_LiteralIndexInAForkArmIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  class Foo;\n"
      "    int id;\n"
      "  endclass\n"
      "  int data[Foo];\n"
      "  int x;\n"
      "  initial begin\n"
      "    fork\n"
      "      x = data[7];\n"
      "    join\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "class-indexed associative array 'data' shall be "
                            "indexed by an object of class 'Foo'",
                            9, "7.8.3"));
}

TEST(ClassIndexAssocArrayElaboration,
     AssocArrayClassIndex_LiteralIndexInAnAssertionPassStatementIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  class Foo;\n"
      "    int id;\n"
      "  endclass\n"
      "  int data[Foo];\n"
      "  int x;\n"
      "  logic ok;\n"
      "  initial assert (ok) x = data[7];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "class-indexed associative array 'data' shall be "
                            "indexed by an object of class 'Foo'",
                            8, "7.8.3"));
}

TEST(ClassIndexAssocArrayElaboration,
     AssocArrayClassIndex_LiteralIndexInAnAssertionFailStatementIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  class Foo;\n"
      "    int id;\n"
      "  endclass\n"
      "  int data[Foo];\n"
      "  int x;\n"
      "  logic ok;\n"
      "  initial assert (ok) else x = data[7];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "class-indexed associative array 'data' shall be "
                            "indexed by an object of class 'Foo'",
                            8, "7.8.3"));
}

TEST(ClassIndexAssocArrayElaboration,
     AssocArrayClassIndex_LiteralIndexInARandcaseItemIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  class Foo;\n"
      "    int id;\n"
      "  endclass\n"
      "  int data[Foo];\n"
      "  int x;\n"
      "  initial randcase 1: x = data[7]; endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "class-indexed associative array 'data' shall be "
                            "indexed by an object of class 'Foo'",
                            7, "7.8.3"));
}

TEST(ClassIndexAssocArrayElaboration,
     AssocArrayClassIndex_LiteralIndexInARandsequenceCodeBlockIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  class Foo;\n"
      "    int id;\n"
      "  endclass\n"
      "  int data[Foo];\n"
      "  int x;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { x = data[7]; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "class-indexed associative array 'data' shall be "
                            "indexed by an object of class 'Foo'",
                            9, "7.8.3"));
}

TEST(ClassIndexAssocArrayElaboration,
     AssocArrayClassIndex_LiteralIndexInAForLoopInitializationIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  class Foo;\n"
      "    int id;\n"
      "  endclass\n"
      "  int data[Foo];\n"
      "  int x;\n"
      "  int i;\n"
      "  initial for (x = data[7]; i < 1; i = i + 1) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "class-indexed associative array 'data' shall be "
                            "indexed by an object of class 'Foo'",
                            8, "7.8.3"));
}

TEST(ClassIndexAssocArrayElaboration,
     AssocArrayClassIndex_LiteralIndexInAForLoopStepIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  class Foo;\n"
      "    int id;\n"
      "  endclass\n"
      "  int data[Foo];\n"
      "  int x;\n"
      "  int i;\n"
      "  initial for (i = 0; i < 1; x = data[7]) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "class-indexed associative array 'data' shall be "
                            "indexed by an object of class 'Foo'",
                            8, "7.8.3"));
}

TEST(ClassIndexAssocArrayElaboration, NonObjectIndexExpressionRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  class K; endclass\n"
      "  int c [K];\n"
      "  string t;\n"
      "  int q[$];\n"
      "  function int f(int x); return x; endfunction\n"
      "  initial begin\n"
      "    c[t.len()] = 1;\n"
      "    c[f(1)] = 1;\n"
      "    c[q.size()] = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "class-indexed associative array 'c' shall be "
                            "indexed by an object of class 'K'",
                            8, "7.8.3"));
}

TEST(ClassIndexAssocArrayElaboration, NonObjectSelectCastAndCallRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  class K; endclass\n"
      "  int c [K];\n"
      "  int a [2];\n"
      "  real ra [2];\n"
      "  K ka [2];\n"
      "  K h;\n"
      "  function string g(); return \"x\"; endfunction\n"
      "  function K mk(); return h; endfunction\n"
      "  initial begin\n"
      "    c[a[0]] = 1;\n"
      "    c[ra[0]] = 1;\n"
      "    c[int'(1)] = 1;\n"
      "    c[{a[0], a[1]}] = 1;\n"
      "    c[g()] = 1;\n"
      "    c[ka[0]] = 1;\n"
      "    c[K'(h)] = 1;\n"
      "    c[mk()] = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  const char* const kReport =
      "class-indexed associative array 'c' shall be indexed by an object of "
      "class 'K'";
  for (uint32_t line = 11; line <= 15; ++line) {
    EXPECT_TRUE(ReportedError(diags, kReport, line, "7.8.3"));
  }
  for (uint32_t line = 16; line <= 18; ++line) {
    EXPECT_FALSE(ReportedError(diags, kReport, line, "7.8.3"));
  }
}

}  // namespace
