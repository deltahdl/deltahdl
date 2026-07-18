#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// 18.5.9: 'constraint_block_item ::= solve solve_before_list before
// solve_before_list ;'. A solve...before ordering with a single variable on
// each side is a well-formed constraint block item and parses without error.
TEST(SolveBeforeOrdering, SingleVariableEachSideAccepted) {
  auto r = Parse(
      "class C;\n"
      "  rand bit s;\n"
      "  rand bit [31:0] d;\n"
      "  constraint c { s -> d == 0; solve s before d; }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
}

// 18.5.9: 'solve_before_list ::= constraint_primary { , constraint_primary }'.
// Each side of the ordering may list several comma-separated variables.
TEST(SolveBeforeOrdering, MultipleVariableListsAccepted) {
  auto r = Parse(
      "class C;\n"
      "  rand int a, b, c, d;\n"
      "  constraint k { solve a, b before c, d; }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
}

// 18.5.9: array.size (with optional following parentheses) is allowed as an
// ordering variable, and a constraint_primary may carry that array built-in
// method call. 'solve A.size() before n' parses.
TEST(SolveBeforeOrdering, ArraySizeMethodAccepted) {
  auto r = Parse(
      "class C;\n"
      "  rand int A[];\n"
      "  rand int n;\n"
      "  constraint k { solve A.size() before n; }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
}

// 18.5.9: 'constraint_primary ::= [ implicit_class_handle . | class_scope ]
// hierarchical_identifier ...'. A primary qualified by an implicit class handle
// (this.) is accepted.
TEST(SolveBeforeOrdering, ImplicitClassHandleQualifierAccepted) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  rand int y;\n"
      "  constraint k { solve this.x before this.y; }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
}

// 18.5.9: a constraint block may contain both regular value constraints and
// ordering constraints. A block mixing an inside constraint, an implication,
// and a solve...before ordering parses as a whole.
TEST(SolveBeforeOrdering, MixedValueAndOrderingConstraintsAccepted) {
  auto r = Parse(
      "class C;\n"
      "  rand bit s;\n"
      "  rand bit [7:0] d;\n"
      "  constraint c {\n"
      "    d inside {[0:200]};\n"
      "    s -> d == 0;\n"
      "    solve s before d;\n"
      "  }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
}

// 18.5.9: more than one ordering statement may appear in a constraint block,
// defining a partial order across several variables. The chained orderings
// parse without error.
TEST(SolveBeforeOrdering, ChainedOrderingStatementsAccepted) {
  auto r = Parse(
      "class C;\n"
      "  rand int a, b, c;\n"
      "  constraint k { solve a before b; solve b before c; }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
}

// 18.5.9: 'constraint_primary ::= [ implicit_class_handle . | class_scope ]
// hierarchical_identifier ...'. The other qualifier alternative — a class_scope
// resolution operator ('::') — on an ordering primary is accepted.
TEST(SolveBeforeOrdering, ClassScopeQualifierAccepted) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  rand int y;\n"
      "  constraint k { solve C::x before y; }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
}

// 18.5.9: 'constraint_primary ::= ... hierarchical_identifier select [ ( ) ]'.
// The production admits an optional 'select' on the ordering primary, so an
// ordering variable named through an element select — such as q[0] on an array
// member — is a well-formed constraint_primary and parses.
TEST(SolveBeforeOrdering, IndexedSelectPrimaryAccepted) {
  auto r = Parse(
      "class C;\n"
      "  rand int q[4];\n"
      "  rand int n;\n"
      "  constraint k { solve q[0] before n; }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
