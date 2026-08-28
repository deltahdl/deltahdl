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

// §7.8.3: an index that is a declared variable of a non-class type (here an
// int) is "any other type" and shall be a type check error, even though it is
// neither a literal nor a wrong-class handle.
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

// §7.8.3: a string variable is likewise a non-class type and an illegal class
// index.
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

// A handle of a class derived from the index class is an accepted index.
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

// §7.8.3: derivation is directional. A base-class handle is neither the
// derived index class nor derived from it, so indexing a derived-index array
// with a base handle is a type check error.
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

// The seven cases below stand in the seven statement positions
// WalkStmtsForClassIndexSelect in
// src/elaborator/elaborator_validate_class_array_index.cpp reached only once it
// took its list of nested statements from ForEachChildStmt in
// src/elaborator/elaborator_validate_internal.h. Each writes the literal index
// AssocArrayClassIndex_LiteralIndexIsError above writes in a plain initial
// statement, and §7.8.3 rules on it the same way wherever it stands. Each
// elaborated clean beforehand.

// A.6.3 gives `par_block ::= fork [ : block_identifier ] {
// block_item_declaration } { statement_or_null } join_keyword [ :
// block_identifier ]`, so a fork arm is a statement position like any other.
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

// §16.3 gives `action_block ::= statement_or_null | [ statement ] else
// statement_or_null`, so an immediate assertion holds a statement in each arm.
// This case covers the pass arm and the one below it the else arm.
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

// §18.16 gives `randcase_item ::= expression : statement_or_null`. The type
// check is a static one, so it holds whether the weighted draw would select
// the item or not.
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

// A.6.12 gives `rs_code_block ::= { { data_declaration } { statement_or_null }
// }`, so a randsequence production's code block holds ordinary procedural
// statements.
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

// A.6.8 gives `for_initialization ::= list_of_variable_assignments | ...` and
// `for_step_assignment ::= operator_assignment | inc_or_dec_expression |
// function_subroutine_call`, so an assignment stands at each of the two
// positions: this case writes one at the initialization and the case below it
// writes one at the step.
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

}  // namespace
