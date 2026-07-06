#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §23.9: an identifier shall be used to declare only one item within a
// scope. Two nets sharing a name in the same module scope is illegal.
TEST(ScopeRulesElaboration, DuplicateIdentifierInSameScopeRejected) {
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  wire w;\n"
             "  wire w;\n"
             "endmodule\n"));
}

// §23.9: the same rule applies to the construct the LRM names first — two
// variable declarations sharing a name in one scope. This exercises the
// variable declaration form rather than the net form above.
TEST(ScopeRulesElaboration, DuplicateVariableDeclarationInSameScopeRejected) {
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  int x;\n"
             "  int x;\n"
             "endmodule\n"));
}

// §23.9 also forbids naming a task the same as a variable in the same
// module scope; the two declarations collide on one identifier.
TEST(ScopeRulesElaboration, TaskNameMatchingVariableRejected) {
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  logic foo;\n"
             "  task foo;\n"
             "  endtask\n"
             "endmodule\n"));
}

// §23.9 spells out one form of that collision explicitly: a gate instance
// shall not share the name of the net connected to its output.
TEST(ScopeRulesElaboration, GateInstanceNameMatchingOutputNetRejected) {
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  wire a, b;\n"
             "  and g1(g1, a, b);\n"
             "endmodule\n"));
}

// §23.9: each module opens a new scope, so the same identifier may name an
// item in two different modules without colliding.
TEST(ScopeRulesElaboration, SameNameInSeparateModuleScopesAllowed) {
  EXPECT_TRUE(
      ElabOk("module child;\n"
             "  wire x;\n"
             "endmodule\n"
             "module top;\n"
             "  wire x;\n"
             "  child c();\n"
             "endmodule\n"));
}

// §23.9: a package is another of the listed constructs that opens its own
// scope, so a name declared in a package does not collide with a like-named
// declaration in a module. Covers a scope-creating construct kind other than
// the module-vs-module case above.
TEST(ScopeRulesElaboration, SameNameInPackageAndModuleScopesAllowed) {
  EXPECT_TRUE(
      ElabOk("package p;\n"
             "  int x;\n"
             "endpackage\n"
             "module m;\n"
             "  int x;\n"
             "endmodule\n"));
}

TEST(ScopeRulesElaboration, ConditionalGenerateBlocksAllowSameIdentifier) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  parameter P = 1;\n"
             "  if (P == 1) begin : g\n"
             "    logic data;\n"
             "  end else begin : g\n"
             "    logic data;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ScopeRulesElaboration, DirectVariableReferenceStopsAtModuleBoundary) {
  EXPECT_FALSE(
      ElabOk("module child;\n"
             "  initial outer_x = 1;\n"
             "endmodule\n"
             "module parent;\n"
             "  logic outer_x;\n"
             "  child c();\n"
             "endmodule\n"));
}

TEST(ScopeRulesElaboration, InstanceNamePrecedenceOverModuleTypeName) {
  EXPECT_TRUE(
      ElabOk("module foo;\n"
             "  integer x;\n"
             "endmodule\n"
             "module top;\n"
             "  foo foo();\n"
             "  initial foo.x = 5;\n"
             "endmodule\n"));
}

// §23.9: a name referenced directly inside a named block that is not declared
// locally triggers an upward search, which continues until the item is found in
// an enclosing scope. Here the write inside block b resolves upward to the
// module-level net, so elaboration succeeds. This is the accepting counterpart
// of DirectVariableReferenceStopsAtModuleBoundary.
TEST(ScopeRulesElaboration, DirectReferenceResolvesUpwardToEnclosingScope) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic sig;\n"
             "  initial begin : b\n"
             "    sig = 1;\n"
             "  end\n"
             "endmodule\n"));
}

// §23.9: a named begin-end block is one of the elements that occupies the
// enclosing scope's namespace, so two blocks sharing a name in the same scope
// declare one identifier twice and are illegal. This is the general rule whose
// only exception is the conditional-generate case tested above.
TEST(ScopeRulesElaboration, DuplicateNamedBlockLabelsInSameScopeRejected) {
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  initial begin : b\n"
             "  end\n"
             "  initial begin : b\n"
             "  end\n"
             "endmodule\n"));
}

}  // namespace
